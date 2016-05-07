use std::{fmt, mem};
use std::ops::{Index, IndexMut, Range, RangeTo, RangeFrom, RangeFull};
use std::borrow::{Borrow, BorrowMut};
use std::error::Error;
use std::ascii::AsciiExt;

use ascii::Ascii;
use ascii_string::AsciiString;

/// AsciiStr represents a byte or string slice that only contains ASCII characters.
///
/// It wraps an `[Ascii]` and implements many of `str`s methods and traits.
///
/// Can be created by a checked conversion from a `str` or `[u8]`,
/// or borrowed from an `AsciiString`.
#[derive(PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AsciiStr {
    slice: [Ascii],
}

impl AsciiStr {
    /// Coerces into an `AsciiStr` slice.
    pub fn new<S: AsRef<AsciiStr> + ?Sized>(s: &S) -> &AsciiStr {
        s.as_ref()
    }

    /// Converts `&self` to a `&str` slice.
    pub fn as_str(&self) -> &str {
        unsafe { mem::transmute(&self.slice) }
    }

    /// Converts `&self` into a byte slice.
    pub fn as_bytes(&self) -> &[u8] {
        unsafe { mem::transmute(&self.slice) }
    }

    /// Returns the entire string as slice of `Ascii` characters.
    pub fn as_slice(&self) -> &[Ascii] {
        &self.slice
    }

    /// Returns the entire string as mutable slice of `Ascii` characters.
    pub fn as_mut_slice(&mut self) -> &mut [Ascii] {
        &mut self.slice
    }

    /// Returns a raw pointer to the `AsciiStr`'s buffer.
    ///
    /// The caller must ensure that the slice outlives the pointer this function returns, or else it
    /// will end up pointing to garbage. Modifying the `AsciiStr` may cause it's buffer to be
    /// reallocated, which would also make any pointers to it invalid.
    pub fn as_ptr(&self) -> *const Ascii {
        self.as_slice().as_ptr()
    }

    /// Returns an unsafe mutable pointer to the `AsciiStr`'s buffer.
    ///
    /// The caller must ensure that the slice outlives the pointer this function returns, or else it
    /// will end up pointing to garbage. Modifying the `AsciiStr` may cause it's buffer to be
    /// reallocated, which would also make any pointers to it invalid.
    pub fn as_mut_ptr(&mut self) -> *mut Ascii {
        self.as_mut_slice().as_mut_ptr()
    }

    /// Copies the content of this `AsciiStr` into an owned `AsciiString`.
    pub fn to_ascii_string(&self) -> AsciiString {
        AsciiString::from(self.slice.to_vec())
    }

    /// Converts anything that can represent a byte slice into an `AsciiStr`.
    ///
    /// # Examples
    /// ```
    /// # use ascii::AsciiStr;
    /// let foo = AsciiStr::from_ascii("foo");
    /// let err = AsciiStr::from_ascii("Ŋ");
    /// assert_eq!(foo.unwrap().as_str(), "foo");
    /// assert_eq!(err.unwrap_err().valid_up_to(), 0);
    /// ```
    pub fn from_ascii<'a, S: 'a+?Sized+AsAsciiStr, T: ?Sized+Borrow<S>>(s: &'a T)
    -> Result<&'a AsciiStr, AsAsciiStrError> {
        s.borrow().as_ascii_str()
    }

    /// Converts anything that can be represented as a byte slice to an `AsciiStr` without checking for non-ASCII characters..
    ///
    /// # Examples
    /// ```
    /// # use ascii::AsciiStr;
    /// let foo = unsafe{ AsciiStr::from_ascii_unchecked("foo") };
    /// assert_eq!(foo.as_str(), "foo");
    /// ```
    pub unsafe fn from_ascii_unchecked<'a, S:'a+?Sized+AsAsciiStr, T:?Sized+Borrow<S>>
    (s: &'a T) -> &'a AsciiStr {
        s.borrow().as_ascii_str_unchecked()
    }


    /// Converts anything that can represent a byte slice into an `AsciiStr`.
    ///
    /// # Examples
    /// ```
    /// # use ascii::AsciiStr;
    /// let foo = AsciiStr::from_mut_ascii("foo");
    /// let err = AsciiStr::from_mut_ascii("Ŋ");
    /// assert_eq!(foo.unwrap().as_str(), "foo");
    /// assert_eq!(err, Err());
    /// ```
    pub fn from_mut_ascii<'a, S: 'a+?Sized+AsMutAsciiStr, T: ?Sized+BorrowMut<S>>
    (s: &'a mut T) -> Result<&'a mut AsciiStr, AsAsciiStrError> {
        s.borrow_mut().as_mut_ascii_str()
    }

    /// Converts anything that can represent a byte slice into an `AsciiStr` without validation.
    ///
    /// # Examples
    /// ```
    /// # use ascii::AsciiStr;
    /// let foo = unsafe{ AsciiStr::from_mut_ascii_unchecked("foo".to_string()) };
    /// assert_eq!(foo.as_str(), "foo");
    /// ```
    pub unsafe fn from_mut_ascii_unchecked<'a, S:'a+?Sized+AsMutAsciiStr, T:?Sized+BorrowMut<S>>
    (s: &'a mut T) -> &'a mut AsciiStr {
        s.borrow_mut().as_mut_ascii_str_unchecked()
    }

    /// Returns the number of characters / bytes in this ASCII sequence.
    ///
    /// # Examples
    /// ```
    /// # use ascii::AsciiStr;
    /// let s = AsciiStr::from_ascii("foo").unwrap();
    /// assert_eq!(s.len(), 3);
    /// ```
    pub fn len(&self) -> usize {
        self.slice.len()
    }

    /// Returns true if the ASCII slice contains zero bytes.
    ///
    /// # Examples
    /// ```
    /// # use ascii::AsciiStr;
    /// let mut empty = AsciiStr::from_ascii("").unwrap();
    /// let mut full = AsciiStr::from_ascii("foo").unwrap();
    /// assert!(empty.is_empty());
    /// assert!(!full.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns an ASCII string slice with leading and trailing whitespace removed.
    ///
    /// # Examples
    /// ```
    /// # use ascii::AsciiStr;
    /// let example = AsciiStr::from_ascii("  \twhite \tspace  \t").unwrap();
    /// assert_eq!("white \tspace", example.trim());
    /// ```
    pub fn trim(&self) -> &Self {
        unsafe { mem::transmute(self.as_str().trim()) }
    }

    /// Returns an ASCII string slice with leading whitespace removed.
    ///
    /// # Examples
    /// ```
    /// # use ascii::AsciiStr;
    /// let example = AsciiStr::from_ascii("  \twhite \tspace  \t").unwrap();
    /// assert_eq!("white \tspace  \t", example.trim_left());
    /// ```
    pub fn trim_left(&self) -> &Self {
        unsafe { mem::transmute(self.as_str().trim_left()) }
    }

    /// Returns an ASCII string slice with trainling whitespace removed.
    ///
    /// # Examples
    /// ```
    /// # use ascii::AsciiStr;
    /// let example = AsciiStr::from_ascii("  \twhite \tspace  \t").unwrap();
    /// assert_eq!("  \twhite \tspace", example.trim_right());
    /// ```
    pub fn trim_right(&self) -> &Self {
        unsafe { mem::transmute(self.as_str().trim_right()) }
    }
}

impl PartialEq<str> for AsciiStr {
    fn eq(&self, other: &str) -> bool {
        self.as_str() == other
    }
}

impl PartialEq<AsciiStr> for str {
    fn eq(&self, other: &AsciiStr) -> bool {
        other.as_str() == self
    }
}

impl ToOwned for AsciiStr {
    type Owned = AsciiString;

    fn to_owned(&self) -> AsciiString {
        self.to_ascii_string()
    }
}

impl AsRef<[u8]> for AsciiStr {
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}
impl AsRef<str> for AsciiStr {
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}
impl AsRef<[Ascii]> for AsciiStr {
    fn as_ref(&self) -> &[Ascii] {
        &self.slice
    }
}
impl AsMut<[Ascii]> for AsciiStr {
    fn as_mut(&mut self) -> &mut[Ascii] {
        &mut self.slice
    }
}

impl Default for &'static AsciiStr {
    fn default() -> &'static AsciiStr {
        unsafe{ "".as_ascii_str_unchecked() }
    }
}
impl<'a> From<&'a[Ascii]> for &'a AsciiStr {
    fn from(slice: &[Ascii]) -> &AsciiStr {
        unsafe{ mem::transmute(slice) }
    }
}
impl<'a> From<&'a mut [Ascii]> for &'a mut AsciiStr {
    fn from(slice: &mut[Ascii]) -> &mut AsciiStr {
        unsafe{ mem::transmute(slice) }
    }
}
impl From<Box<[Ascii]>> for Box<AsciiStr> {
    fn from(owned: Box<[Ascii]>) -> Box<AsciiStr> {
        unsafe{ mem::transmute(owned) }
    }
}

macro_rules! impl_into {
    ($wider: ty) => {
        impl<'a> From<&'a AsciiStr> for &'a$wider {
            fn from(slice: &AsciiStr) -> &$wider {
                unsafe{ mem::transmute(slice) }
            }
        }
        impl<'a> From<&'a mut AsciiStr> for &'a mut $wider {
            fn from(slice: &mut AsciiStr) -> &mut $wider {
                unsafe{ mem::transmute(slice) }
            }
        }
        impl From<Box<AsciiStr>> for Box<$wider> {
            fn from(owned: Box<AsciiStr>) -> Box<$wider> {
                unsafe{ mem::transmute(owned) }
            }
        }
    }
}
impl_into! {[Ascii]}
impl_into! {[u8]}
impl_into! {str}

impl fmt::Display for AsciiStr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(self.as_str(), f)
    }
}

impl fmt::Debug for AsciiStr {
   fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
       fmt::Debug::fmt(self.as_str(), f)
   }
}

macro_rules! impl_index {
    ($lhs:ty, $idx:ty, $rhs:ty) => {
        impl Index<$idx> for $lhs {
            type Output = $rhs;

            #[inline]
            fn index(&self, index: $idx) -> &$rhs {
                unsafe { mem::transmute(&self.slice[index]) }
            }
        }

        impl IndexMut<$idx> for $lhs {
            #[inline]
            fn index_mut(&mut self, index: $idx) -> &mut $rhs {
                unsafe { mem::transmute(&mut self.slice[index]) }
            }
        }
    }
}

impl_index! { AsciiStr, usize, Ascii }
impl_index! { AsciiStr, Range<usize>, AsciiStr }
impl_index! { AsciiStr, RangeTo<usize>, AsciiStr }
impl_index! { AsciiStr, RangeFrom<usize>, AsciiStr }
impl_index! { AsciiStr, RangeFull, AsciiStr }

impl AsciiExt for AsciiStr {
    type Owned = AsciiString;

    #[inline]
    fn is_ascii(&self) -> bool {
        true
    }

    fn to_ascii_uppercase(&self) -> AsciiString {
        let mut ascii_string = self.to_ascii_string();
        ascii_string.make_ascii_uppercase();
        ascii_string
    }

    fn to_ascii_lowercase(&self) -> AsciiString {
        let mut ascii_string = self.to_ascii_string();
        ascii_string.make_ascii_uppercase();
        ascii_string
    }

    fn eq_ignore_ascii_case(&self, other: &Self) -> bool {
        self.len() == other.len() &&
        self.slice.iter().zip(other.slice.iter()).all(|(a, b)| a.eq_ignore_ascii_case(b))
    }

    fn make_ascii_uppercase(&mut self) {
        for ascii in &mut self.slice {
            ascii.make_ascii_uppercase();
        }
    }

    fn make_ascii_lowercase(&mut self) {
        for ascii in &mut self.slice {
            ascii.make_ascii_lowercase();
        }
    }
}


/// Error that is returned when a sequence of `u8` are not all ASCII.
///
/// Is used by `As[Mut]AsciiStr` and the `from_ascii` method on `AsciiStr` and `AsciiString`.
#[derive(Clone,Copy)]
pub struct AsAsciiStrError {
    index: usize,
    /// If less than 128, it was a byte >= 128 and not from a str
    not_ascii: char,
}

fn first_utf8_byte(not_ascii: char) -> u8 {
    // Not the prettiest solution, but works on Rust 1.9 and no_std.
    // Moved out of .byte() to be testable.
    let len = not_ascii.len_utf8();
    let encoded_bits = not_ascii as u32 >> (len-1)*6;
    let len_encoded = (0xff_00 >> len) as u8;
    len_encoded | encoded_bits as u8
}

impl AsAsciiStrError {
    /// Returns the index of the first non-ASCII byte.
    ///
    /// It is the maximum index such that `from_ascii(input[..index])` would return `Ok(_)`.
    pub fn valid_up_to(self) -> usize {
        self.index
    }

    /// If it was a `str` that was being converted, the first byte in the utf8 encoding is returned.
    pub fn byte(self) -> u8 {
        if self.not_ascii < 128 as char {
            self.not_ascii as u8 + 128
        } else {
            first_utf8_byte(self.not_ascii)
        }
    }

    /// Get the character that caused the conversion from a `str` to fail.
    ///
    /// Returns `None` if the error was caused by a byte in a `[u8]`
    pub fn char(self) -> Option<char> {
        match self.not_ascii as u32 {
            0...127 => None, // byte in a [u8]
               _    => Some(self.not_ascii),
        }
    }
}

/// Compares index and `.byte()`s
impl PartialEq for AsAsciiStrError {
    fn eq(&self, rhs: &Self) -> bool {
        self.index == rhs.index  &&  self.byte() == rhs.byte()
    }
}

impl fmt::Debug for AsAsciiStrError {
    fn fmt(&self,  fmtr: &mut fmt::Formatter) -> fmt::Result {
        if (self.not_ascii as u32) < 128 {
            write!(fmtr, "b'\\x{:x}' at index {}", self.not_ascii as u8 + 128, self.index)
        } else {
            write!(fmtr, "'{}' at index {}", self.not_ascii, self.index)
        }
    }
}
impl fmt::Display for AsAsciiStrError {
    fn fmt(&self,  fmtr: &mut fmt::Formatter) -> fmt::Result {
        if (self.not_ascii as u32) < 128 {
            write!(fmtr, "the byte \\x{:x} at index {} is not ASCII", self.not_ascii as u8 + 128, self.index)
        } else {
            write!(fmtr, "the character {} at index {} is not ASCII", self.not_ascii, self.index)
        }
    }
}
impl Error for AsAsciiStrError {
    /// Returns "one or more bytes are not ASCII"
    /// or "one or more characters are not ASCII"
    fn description(&self) -> &'static str {
        if (self.not_ascii as u32) < 128 {
            "one or more bytes are not ASCII"
        } else {
            "one or more characters are not ASCII"
        }
    }
}


/// Connvert mutable slices of bytes to `AsciiStr`.
pub trait AsAsciiStr : AsciiExt {
    /// Convert to an ASCII slice without checking for non-ASCII characters.
    unsafe fn as_ascii_str_unchecked(&self) -> &AsciiStr;
    /// Convert to an ASCII slice.
    fn as_ascii_str(&self) -> Result<&AsciiStr,AsAsciiStrError>;
}
/// Connvert mutable slices of bytes to `AsciiStr`.
pub trait AsMutAsciiStr : AsciiExt {
    /// Convert to a mutable ASCII slice without checking for non-ASCII characters.
    unsafe fn as_mut_ascii_str_unchecked(&mut self) -> &mut AsciiStr;
    /// Convert to a mutable ASCII slice.
    fn as_mut_ascii_str(&mut self) -> Result<&mut AsciiStr,AsAsciiStrError>;
}

impl AsAsciiStr for AsciiStr {
    fn as_ascii_str(&self) -> Result<&AsciiStr,AsAsciiStrError> {
        Ok(self)
    }
    unsafe fn as_ascii_str_unchecked(&self) -> &AsciiStr {
        self
    }
}
impl AsMutAsciiStr for AsciiStr {
    fn as_mut_ascii_str(&mut self) -> Result<&mut AsciiStr,AsAsciiStrError> {
        Ok(self)
    }
    unsafe fn as_mut_ascii_str_unchecked(&mut self) -> &mut AsciiStr {
        self
    }
}

// Cannot implement for [Ascii] since AsciiExt isn't implementet for it.

impl AsAsciiStr for [u8] {
    fn as_ascii_str(&self) -> Result<&AsciiStr,AsAsciiStrError> {
        match self.iter().enumerate().find(|&(_,b)| *b > 127 ) {
            Some((index, &byte)) => Err(AsAsciiStrError{
                                            index: index,
                                            not_ascii: (byte - 128) as char,
                                        }),
            None => unsafe{ Ok(self.as_ascii_str_unchecked()) },
        }
    }
    unsafe fn as_ascii_str_unchecked(&self) -> &AsciiStr {
        mem::transmute(self)
    }
}
impl AsMutAsciiStr for [u8] {
    fn as_mut_ascii_str(&mut self) -> Result<&mut AsciiStr,AsAsciiStrError> {
        match self.iter().enumerate().find(|&(_,b)| *b > 127 ) {
            Some((index, &byte)) => Err(AsAsciiStrError{
                                            index: index,
                                            not_ascii: (byte - 128) as char,
                                        }),
            None => unsafe{ Ok(self.as_mut_ascii_str_unchecked()) },
        }
    }
    unsafe fn as_mut_ascii_str_unchecked(&mut self) -> &mut AsciiStr {
        mem::transmute(self)
    }
}

impl AsAsciiStr for str {
    fn as_ascii_str(&self) -> Result<&AsciiStr,AsAsciiStrError> {
        match self.bytes().position(|b| b > 127 ) {
            Some(index) => Err(AsAsciiStrError{
                                   index: index,
                                   not_ascii: self[index..].chars().next().unwrap(),
                               }),
            None => unsafe{ Ok(self.as_ascii_str_unchecked()) },
        }
    }
    unsafe fn as_ascii_str_unchecked(&self) -> &AsciiStr {
        self.as_bytes().as_ascii_str_unchecked()
    }
}
impl AsMutAsciiStr for str {
    fn as_mut_ascii_str(&mut self) -> Result<&mut AsciiStr,AsAsciiStrError> {
        match self.bytes().position(|b| b > 127 ) {
            Some(index) => Err(AsAsciiStrError{
                                   index: index,
                                   not_ascii: self[index..].chars().next().unwrap(),
                               }),
            None => unsafe{ Ok(self.as_mut_ascii_str_unchecked()) },
        }
    }
    unsafe fn as_mut_ascii_str_unchecked(&mut self) -> &mut AsciiStr {
        mem::transmute(self)
    }
}


#[cfg(test)]
mod tests {
    use Ascii;
    use super::{AsciiStr,AsAsciiStr,AsMutAsciiStr,AsAsciiStrError};

    #[test]
    fn generic_as_ascii_str() {
        fn generic<C:AsAsciiStr+?Sized>(c: &C) -> Result<&AsciiStr,AsAsciiStrError> {
            c.as_ascii_str()
        }
        let arr = [Ascii::A];
        let ascii_str: &AsciiStr = arr.as_ref().into();
        assert_eq!(generic("A"), Ok(ascii_str));
        assert_eq!(generic(&b"A"[..]), Ok(ascii_str));
        assert_eq!(generic(ascii_str), Ok(ascii_str));
    }

    #[test]
    fn as_ascii_str() {
        /// AsAsciiStrError doesn't compare not_ascii, but .byte()
        macro_rules! tuplify{ {$result:expr} => {
            $result.map_err(|aase| (aase.index, aase.not_ascii) )
        }}
        let mut s: String = "abčd".to_string();
        let mut b: Vec<u8> = s.clone().into();
        assert_eq!(tuplify!(s.as_str().as_ascii_str()), Err((2, 'č')));
        assert_eq!(tuplify!(s.as_mut_str().as_mut_ascii_str()), Err((2, 'č')));
        let c = (b[2]-128) as char;
        assert_eq!(tuplify!(b.as_slice().as_ascii_str()), Err((2, c)));
        assert_eq!(tuplify!(b.as_mut_slice().as_mut_ascii_str()), Err((2, c)));

        let mut a = [Ascii::a, Ascii::b];
        assert_eq!((&s[..2]).as_ascii_str(), Ok((&a[..]).into()));
        assert_eq!((&b[..2]).as_ascii_str(), Ok((&a[..]).into()));
        let a = Ok((&mut a[..]).into());
        assert_eq!((&mut s[..2]).as_mut_ascii_str(), a);
        assert_eq!((&mut b[..2]).as_mut_ascii_str(), a);
    }

    #[test]
    fn first_utf8_byte() {
        let s = "¡߹ऄ￮𐄂𠂤";
        for (i,c) in s.char_indices() {
            assert_eq!(super::first_utf8_byte(c), s.as_bytes()[i]);
        }
    }

    #[test]
    fn default() {
        let default: &'static AsciiStr = Default::default();
        assert!(default.is_empty());
    }

    #[test]
    fn as_str() {
        let b = b"( ;";
        let v = AsciiStr::from_ascii(b).unwrap();
        assert_eq!(v.as_str(), "( ;");
        assert_eq!(AsRef::<str>::as_ref(v), "( ;");
    }

    #[test]
    fn as_bytes() {
        let b = b"( ;";
        let v = AsciiStr::from_ascii(b).unwrap();
        assert_eq!(v.as_bytes(), b"( ;");
        assert_eq!(AsRef::<[u8]>::as_ref(v), b"( ;");
    }

    #[test]
    fn fmt_ascii_str() {
        let s = "abc".as_ascii_str().unwrap();
        assert_eq!(format!("{}", s), "abc".to_string());
        assert_eq!(format!("{:?}", s), "\"abc\"".to_string());
    }
}
