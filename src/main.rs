//! Urbit Nock 4K data structures, with basic parsing, and evaluation.
//! <https://urbit.org/docs/learn/arvo/nock/>
#![feature(never_type, exact_size_is_empty)]
use byteorder::{ByteOrder, LittleEndian};
use derive_more::From;
use env_logger;
use log::{debug, error, info, log, trace, warn};
use std::{clone::Clone, error::Error, fmt::Display, rc::Rc};

pub fn main() -> Result<(), Box<dyn std::error::Error>> {
    env_logger::try_init()?;

    let subject = list(&[cell(atom(11), atom(12)), atom(2), atom(3), atom(4), atom(5)]);
    let formula = (atom(0), atom(7));

    info!("subject: {}", subject);
    info!("formula: {}", Noun::from(formula.clone()));

    let product = nock(&subject, &formula)?;

    info!("product: {}.", &product);

    println!("*[{} {}] = {}", subject, Noun::from(formula.clone()), product);

    Ok(())
}

/* Data structures * * * * * * * * * * * * * * * * * */

/// A Nock Noun can be any Nock value, either an Atom or a Cell.
#[derive(Debug, Hash, Eq, PartialEq, Clone)]
pub enum Noun {
    Atom(Rc<Atom>),
    Cell(Rc<Cell>),
}

/// A Nock Cell is an ordered pair of Nouns, implemented as a tuple.
pub type Cell = (Noun, Noun);

/// A Nock Atom is an arbitrarily-large unsigned integer.
#[derive(Debug, Hash, Eq, PartialEq, Clone)]
pub struct Atom {
    bytes_le: Vec<u8>,
}

/// Evaluating a Nock expression that contains an invalid, undefined, infinite,
/// nonterminating, or irreducible subexpression produces a Crash.
#[derive(Debug, Hash, Eq, PartialEq, Clone, From)]
pub struct Crash {
    message: String,
}

/* Atom encoding and decoding * * * * * * * * * * * * * * * * * */

impl Atom {
    /// Construct a new Atom from a little-endian byte slice.
    pub fn new(bytes_le: &[u8]) -> Self {
        // Strip irrelevent trailing zero bytes to normalize Atom for Hash and Eq.
        let mut len = bytes_le.len();
        while len > 0 && bytes_le[len - 1] == 0x00 {
            len -= 1;
        }
        Self { bytes_le: bytes_le[..len].to_vec() }
    }

    /// Whether this Atom is zero, which is the truthy value in Nock.
    pub fn is_zero(&self) -> bool {
        self.bytes_le.len() == 0
    }

    /// Returns the value of this atom as a little-endian byte slice.
    pub fn as_bytes_le(&self) -> &[u8] {
        &self.bytes_le
    }

    /// Returns the value of the atom as Some(u128) if it fits, else None.
    pub fn try_u128(&self) -> Option<u128> {
        if self.as_bytes_le().is_empty() {
            Some(0)
        } else if self.bytes_le.len() < 16 {
            Some(LittleEndian::read_uint128(&self.bytes_le, self.bytes_le.len()))
        } else {
            None
        }
    }
}

impl From<bool> for Atom {
    fn from(b: bool) -> Atom {
        if b {
            Atom::new(&[0])
        } else {
            Atom::new(&[1])
        }
    }
}

impl From<u128> for Atom {
    fn from(n: u128) -> Atom {
        let mut bytes = [0u8; 16];
        LittleEndian::write_u128(&mut bytes, n);
        Atom::new(&bytes)
    }
}

/* Noun construction conveniences * * * * * * * * * * * * * * * * * */

impl From<Atom> for Noun {
    fn from(atom: Atom) -> Noun {
        Noun::Atom(Rc::new(atom))
    }
}

impl From<Cell> for Noun {
    fn from(cell: Cell) -> Noun {
        Noun::Cell(Rc::new(cell))
    }
}

/// Creates a new cons Cell Noun containing two existing Nouns.
pub fn cell(left: Noun, right: Noun) -> Noun {
    (left, right).into()
}

/// Creates a new unsigned integer Atom Noun.
pub fn atom<T: Into<Atom>>(atom: T) -> Noun {
    atom.into().into()
}

/// Groups a nonempty slice of Nouns into Cells, from right-to-left, returning a Noun.
///
/// `list(&[a, b, c, d, ...])` = `cell(a, cell(b, cell(c, cell(d, ...))))`
pub fn list(nouns: &[Noun]) -> Noun {
    let nouns = nouns.to_vec();
    if nouns.is_empty() {
        panic!("can't have an empty list")
    }
    let mut nouns_rev = nouns.into_iter().rev();
    let mut result = nouns_rev.next().unwrap();
    for outer in nouns_rev {
        result = cell(outer, result);
    }
    result
}

/* Formatting nouns and errors * * * * * * * * * * * * * * * * * */

impl Display for Noun {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Noun::Atom(atom) => match atom.try_u128() {
                // If it fits in u128 we'll display it as an ordinary decimal integer
                // literal.
                Some(n) => write!(f, "{}", n),
                // For larger values, we'll use a hex integer literal.
                None => {
                    write!(f, "0x")?;
                    for byte in atom.as_bytes_le().iter().rev() {
                        write!(f, "{:02x}", byte)?;
                    }
                    Ok(())
                }
            },
            Noun::Cell(cell) => {
                let (ref head, ref tail) = **cell;
                write!(f, "[{} {}]", head, tail)
            }
        }
    }
}

impl Error for Crash {}
impl Display for Crash {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "Nock Crash: {}", self.message)
    }
}
impl From<&str> for Crash {
    fn from(message: &str) -> Crash {
        message.to_string().into()
    }
}

/* Nock evaluation * * * * * * * * * * * * * * * * * */

/// The Nock function interprets a formula Cell and applies it a subject Noun.
pub fn nock(subject: &Noun, formula: &Cell) -> Result<Noun, Crash> {
    let (ref operation, ref parameter) = formula;
    match operation {
        // [*[a b c] *[a d]]
        Noun::Cell(cell_) => {
            let (f, g) = &*cell_.clone();
            let fp = nock(subject, &*f.cell()?)?;
            let gp = nock(subject, &*g.cell()?)?;
            Ok(cell(fp, gp))
        }
        Noun::Atom(atom) => match atom.try_u128().ok_or(Crash::from("opcode > u128"))? {
            // A formula [0 b] reduces to the noun at tree address b in the subject.
            // *[a 0 b]  ->  /[b a]
            0 => cell(parameter.clone(), subject.clone()).net(),
            // A formula [1 b] reduces to the constant noun b.
            // *[a 1 b]  ->  b
            1 => Ok(parameter.clone()),
            // A formula [2 b c] treats b and c as formulas, resolves each against the
            // subject, then computes Nock again with the product of b as the subject, c
            // as the formula. *[a 2 b c]  ->  *[*[a b] *[a c]]
            2 => {
                let (f, g) = &*parameter.cell()?.clone();
                let fp = nock(subject, &*f.cell()?)?;
                let gp = nock(subject, &*g.cell()?)?;
                nock(&fp, &*gp.cell()?)
            }
            // In formulas [3 b] and [4 b], b is another formula, whose product against
            // the subject becomes the input to an axiomatic operator. 3 is ? and 4 is +
            // *[a 3 b]  ->  ?*[a b]
            3 => Ok(cell(subject.clone(), parameter.clone()).tar()?.wut().into()),
            // *[a 4 b]  ->  +*[a b]
            4 => Ok(cell(subject.clone(), parameter.clone()).tar()?.lus()?.into()),
            // A formula [5 b c] treats b and c as formulas that become the input to
            // another axiomatic operator, =. *[a 5 b c]  ->  =[*[a b]
            // *[a c]]
            5 => unimplemented!(),
            // Instructions 6 through 11 are not strictly necessary for Turing
            // completeness; deleting them from Nock would decrease compactness, but not
            // expressiveness. [6 b c d] is if b, then c, else d. Each
            // of b, c, d is a formula against the subject. Remember that 0 is true and
            // 1 is false. *[a 6 b c d]  ->  *[a *[[c d] 0 *[[2 3] 0 *[a
            // 4 4 b]]]]
            6 => unimplemented!(),
            // [7 b c] composes the formulas b and c.
            // *[a 7 b c]  ->  *[*[a b] c]
            7 => unimplemented!(),
            // [8 b c] produces the product of formula c, against a subject whose head
            // is the product of formula b with the original subject, and whose tail is
            // the original subject. (Think of 8 as a “variable declaration” or “stack
            // push.”) *[a 8 b c]  ->  *[[*[a b] a] c]
            8 => unimplemented!(),
            // [9 b c] computes the product of formula c with the current subject; from
            // that product d it extracts a formula e at tree address b, then computes
            // *[d e]. (9 is designed to fit Hoon; d is a core (object), e points to an
            // arm (method).) *[a 9 b c]  ->  *[*[a c] 2 [0 1] 0 b]
            9 => unimplemented!(),
            // In a formula [10 [b c] d], c and d are computed with the current subject,
            // and then b of the product of d is replaced with the product of c.
            // *[a 10 [b c] d]  ->  #[b *[a c] *[a d]]
            10 => unimplemented!(),
            // [11 b c] is a hint semantically equivalent to the formula c. If b is an
            // atom, it's a static hint, which is just discarded. If b is a cell, it's a
            // dynamic hint; the head of b is discarded, and the tail of b is executed
            // as a formula against the current subject; the product of this is
            // discarded. *[a 11 b c]  ->  *[a c]
            // [11 hint formula]
            11 => {
                let (ref _hint, ref formula) = *parameter.cell()?;
                nock(subject, &*formula.cell()?)
            }
            _ => Err(Crash::from("opcode > 11")),
        },
    }
}

impl Noun {
    /// Returns a reference to the Atom in this Noun, or a Crash if it's a cell.
    pub fn atom(&self) -> Result<Rc<Atom>, Crash> {
        match self {
            Noun::Atom(atom) => Ok(atom.clone()),
            Noun::Cell(_) => Err(Crash::from("expected atom, had cell")),
        }
    }

    /// Returns a reference to the Cell in this Noun, or a Crash if it's an atom.
    pub fn cell(&self) -> Result<Rc<Cell>, Crash> {
        match self {
            Noun::Cell(cell) => Ok(cell.clone()),
            Noun::Atom(_) => Err(Crash::from("expected cell, had atom")),
        }
    }

    /// `*[subject formula]` nock formula application.
    pub fn tar(&self) -> Result<Noun, Crash> {
        trace!("*{}", self);
        let (ref subject, ref formula) = *self.cell()?;
        nock(subject, &*formula.cell()?)
    }

    /// `?noun` noun type operator.
    pub fn wut(&self) -> Atom {
        trace!("?{}", self);
        match self {
            Noun::Cell(_) => true,
            Noun::Atom(_) => false,
        }.into()
    }

    /// `=[head tail]` noun equality operator.
    pub fn tis(&self) -> Result<Atom, Crash> {
        trace!("={}", self);
        let (ref head, ref tail) = *self.cell()?;
        Ok((head == tail).into())
    }

    /// `+number` atom increment operator.
    pub fn lus(&self) -> Result<Atom, Crash> {
        trace!("+{}", self);
        let atom = self.atom()?;
        let mut incremented_bytes = atom.as_bytes_le().to_vec();
        incremented_bytes.push(0x00);
        for byte in incremented_bytes.iter_mut() {
            if *byte == 0xFF {
                *byte = 0x00;
                continue;
            } else {
                *byte += 1;
                break;
            }
        }
        Ok(Atom::new(&incremented_bytes))
    }

    /// `/[index root]`, `*[root 0 index]` cell tree slot indexing operator.
    pub fn net(&self) -> Result<Noun, Crash> {
        trace!("/{}", self);
        let (ref index, ref root) = *self.cell()?;
        let index = index.atom()?.clone();
        if index.is_zero() {
            return Err(Crash::from("index in /[index root] must be > 0"));
        }
        let mut result = root.clone();
        for (byte_index, byte) in index.as_bytes_le().iter().rev().enumerate() {
            let skip_bits = if byte_index == 0 {
                byte.leading_zeros() + 1
            } else {
                0
            };
            for bit_index in skip_bits..8 {
                result = if ((byte >> (7 - bit_index)) & 1) == 0 {
                    result.cell()?.0.clone()
                } else {
                    result.cell()?.1.clone()
                };
            }
        }
        Ok(result)
    }

    /// `#[index root replacement]` edit cell tree index modification operator.
    pub fn hax(&self) -> Result<Atom, Crash> {
        trace!("#{}", self);
        unimplemented!()
    }
}
