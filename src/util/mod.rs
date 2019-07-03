use std::fmt;
use std::error;
use std::io;
use std::io::{
    Read,
    Write,
    Seek,
    SeekFrom,
    Cursor
};

use std::char::from_digit;
use std::marker::PhantomData;
use std::ops::{Deref, DerefMut};
use std::collections::HashMap;
use std::collections::VecDeque;
use std::collections::HashSet;

use std::fs;
use std::path::{
    Path,
    PathBuf
};

use std::ptr;
use std::ffi::OsStr;

use sha2::Sha512Trunc256;
use sha2::Digest;

/// Borrowed from Andrew Poelstra's rust-bitcoin
macro_rules! impl_array_newtype {
    ($thing:ident, $ty:ty, $len:expr) => {
        impl $thing {
            #[inline]
            #[allow(dead_code)]
            /// Converts the object to a raw pointer
            pub fn as_ptr(&self) -> *const $ty {
                let &$thing(ref dat) = self;
                dat.as_ptr()
            }

            #[inline]
            #[allow(dead_code)]
            /// Converts the object to a mutable raw pointer
            pub fn as_mut_ptr(&mut self) -> *mut $ty {
                let &mut $thing(ref mut dat) = self;
                dat.as_mut_ptr()
            }

            #[inline]
            #[allow(dead_code)]
            /// Returns the length of the object as an array
            pub fn len(&self) -> usize { $len }

            #[inline]
            #[allow(dead_code)]
            /// Returns whether the object, as an array, is empty. Always false.
            pub fn is_empty(&self) -> bool { false }

            #[inline]
            #[allow(dead_code)]
            /// Returns the underlying bytes.
            pub fn as_bytes(&self) -> &[$ty; $len] { &self.0 }

            #[inline]
            #[allow(dead_code)]
            /// Returns the underlying bytes.
            pub fn to_bytes(&self) -> [$ty; $len] { self.0.clone() }

            #[inline]
            #[allow(dead_code)]
            /// Returns the underlying bytes.
            pub fn into_bytes(self) -> [$ty; $len] { self.0 }
        }

        impl<'a> From<&'a [$ty]> for $thing {
            fn from(data: &'a [$ty]) -> $thing {
                assert_eq!(data.len(), $len);
                let mut ret = [0; $len];
                ret.copy_from_slice(&data[..]);
                $thing(ret)
            }
        }

        impl ::std::ops::Index<usize> for $thing {
            type Output = $ty;

            #[inline]
            fn index(&self, index: usize) -> &$ty {
                let &$thing(ref dat) = self;
                &dat[index]
            }
        }

        impl_index_newtype!($thing, $ty);

        impl PartialEq for $thing {
            #[inline]
            fn eq(&self, other: &$thing) -> bool {
                &self[..] == &other[..]
            }
        }

        impl Eq for $thing {}

        impl PartialOrd for $thing {
            #[inline]
            fn partial_cmp(&self, other: &$thing) -> Option<::std::cmp::Ordering> {
                Some(self.cmp(&other))
            }
        }

        impl Ord for $thing {
            #[inline]
            fn cmp(&self, other: &$thing) -> ::std::cmp::Ordering {
                // manually implement comparison to get little-endian ordering
                // (we need this for our numeric types; non-numeric ones shouldn't
                // be ordered anyway except to put them in BTrees or whatever, and
                // they don't care how we order as long as we're consisistent).
                for i in 0..$len {
                    if self[$len - 1 - i] < other[$len - 1 - i] { return ::std::cmp::Ordering::Less; }
                    if self[$len - 1 - i] > other[$len - 1 - i] { return ::std::cmp::Ordering::Greater; }
                }
                ::std::cmp::Ordering::Equal
            }
        }

        #[cfg_attr(feature = "clippy", allow(expl_impl_clone_on_copy))] // we don't define the `struct`, we have to explicitly impl
        impl Clone for $thing {
            #[inline]
            fn clone(&self) -> $thing {
                $thing::from(&self[..])
            }
        }

        impl Copy for $thing {}

        impl ::std::hash::Hash for $thing {
            #[inline]
            fn hash<H>(&self, state: &mut H)
                where H: ::std::hash::Hasher
            {
                (&self[..]).hash(state);
            }

            fn hash_slice<H>(data: &[$thing], state: &mut H)
                where H: ::std::hash::Hasher
            {
                for d in data.iter() {
                    (&d[..]).hash(state);
                }
            }
        }
    }
}

macro_rules! impl_index_newtype {
    ($thing:ident, $ty:ty) => {
        impl ::std::ops::Index<::std::ops::Range<usize>> for $thing {
            type Output = [$ty];

            #[inline]
            fn index(&self, index: ::std::ops::Range<usize>) -> &[$ty] {
                &self.0[index]
            }
        }

        impl ::std::ops::Index<::std::ops::RangeTo<usize>> for $thing {
            type Output = [$ty];

            #[inline]
            fn index(&self, index: ::std::ops::RangeTo<usize>) -> &[$ty] {
                &self.0[index]
            }
        }

        impl ::std::ops::Index<::std::ops::RangeFrom<usize>> for $thing {
            type Output = [$ty];

            #[inline]
            fn index(&self, index: ::std::ops::RangeFrom<usize>) -> &[$ty] {
                &self.0[index]
            }
        }

        impl ::std::ops::Index<::std::ops::RangeFull> for $thing {
            type Output = [$ty];

            #[inline]
            fn index(&self, _: ::std::ops::RangeFull) -> &[$ty] {
                &self.0[..]
            }
        }
    }
}

macro_rules! impl_array_hexstring_fmt {
    ($thing:ident) => {
        impl ::std::fmt::Debug for $thing {
            fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                let &$thing(data) = self;
                for ch in data.iter() {
                    write!(f, "{:02x}", ch)?;
                }
                Ok(())
            }
        }
    }
}

#[allow(unused_macros)]
macro_rules! impl_byte_array_newtype {
    ($thing:ident, $ty:ty, $len:expr) => {
        impl $thing {
            /// Instantiates from a hex string 
            #[allow(dead_code)]
            pub fn from_hex(hex_str: &str) -> Result<$thing, usize> {
                let _hex_len = $len * 2;
                match (hex_str.len(), hex_bytes(hex_str)) {
                    (_hex_len, Ok(bytes)) => {
                        if bytes.len() != $len {
                            return Err(bytes.len());
                        }
                        let mut ret = [0; $len];
                        ret.copy_from_slice(&bytes);
                        Ok($thing(ret))
                    },
                    (_, Err(_e)) => {
                        Err(0)
                    }
                }
            }
            
            /// Instantiates from a slice of bytes 
            #[allow(dead_code)]
            pub fn from_bytes(inp: &[u8]) -> Option<$thing> {
                match inp.len() {
                    $len => {
                        let mut ret = [0; $len];
                        ret.copy_from_slice(inp);
                        Some($thing(ret))
                    },
                    _ => None
                }
            }

            /// Instantiates from a slice of bytes, converting to host byte order
            #[allow(dead_code)]
            pub fn from_bytes_be(inp: &[u8]) -> Option<$thing> {
                $thing::from_vec_be(&inp.to_vec())
            }

            /// Instantiates from a vector of bytes
            #[allow(dead_code)]
            pub fn from_vec(inp: &Vec<u8>) -> Option<$thing> {
                match inp.len() {
                    $len => {
                        let mut ret = [0; $len];
                        let bytes = &inp[..inp.len()];
                        ret.copy_from_slice(&bytes);
                        Some($thing(ret))
                    },
                    _ => None
                }
            }

            /// Instantiates from a big-endian vector of bytes, converting to host byte order
            #[allow(dead_code)]
            pub fn from_vec_be(b: &Vec<u8>) -> Option<$thing> {
                match b.len() {
                    $len => {
                        let mut ret = [0; $len];
                        let bytes = &b[0..b.len()];
                        // flip endian to le if we are le
                        for i in 0..$len {
                            ret[$len - 1 - i] = bytes[i];
                        }
                        Some($thing(ret))
                    }
                    _ => None
                }
            }

            /// Convert to a hex string 
            #[allow(dead_code)]
            pub fn to_hex(&self) -> String {
                to_hex(&self.0)
            }
        }
    }
}

const PERF_TEST: bool = false;

// print debug statements while testing
#[allow(unused_macros)]
macro_rules! test_debug {
    ($($arg:tt)*) => ({
        use std::env;
        if !PERF_TEST && env::var("BLOCKSTACK_DEBUG") == Ok("1".to_string()) {
            let file = file!();
            let lineno = line!();
            let s1 = format!("[{}:{}] ", file, lineno);
            let s2 = format!($($arg)*);
            eprintln!("{} {}", s1, s2);
        }
    })
}

// Borrowed from Andrew Poelstra's rust-bitcoin library
/// An iterator that returns pairs of elements
pub struct Pair<I>
    where I: Iterator
{
    iter: I,
    last_elem: Option<I::Item>
}

impl<I: Iterator> Iterator for Pair<I> {
    type Item = (I::Item, I::Item);

    #[inline]
    fn next(&mut self) -> Option<(I::Item, I::Item)> {
        let elem1 = self.iter.next();
        if elem1.is_none() {
            None
        } else {
            let elem2 = self.iter.next();
            if elem2.is_none() {
                self.last_elem = elem1;
                None
            } else {
                Some((elem1.unwrap(), elem2.unwrap()))
            }
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        match self.iter.size_hint() {
            (n, None) => (n/2, None),
            (n, Some(m)) => (n/2, Some(m/2))
        }
    }
}

impl<I: Iterator> Pair<I> {
    /// Returns the last element of the iterator if there were an odd
    /// number of elements remaining before it was Pair-ified.
    #[inline]
    pub fn remainder(self) -> Option<I::Item> {
        self.last_elem
    }
}

/// Returns an iterator that returns elements of the original iterator 2 at a time
pub trait Pairable : Sized + Iterator {
    /// Returns an iterator that returns elements of the original iterator 2 at a time
    fn pair(self) -> Pair<Self>;
}

impl<I: Iterator> Pairable for I {
    /// Creates an iterator that yields pairs of elements from the underlying
    /// iterator, yielding `None` when there are fewer than two elements to
    /// return.
    #[inline]
    fn pair(self) -> Pair<I> {
        Pair {iter: self, last_elem: None }
    }
}

pub fn hex_bytes(s: &str) -> Result<Vec<u8>, &'static str> {
    let mut v = vec![];
    let mut iter = s.chars().pair();
    // Do the parsing
    iter.by_ref().fold(Ok(()), |e, (f, s)| 
        if e.is_err() { e }
        else {
            match (f.to_digit(16), s.to_digit(16)) {
                (None, _) => Err("unexpected hex digit"),
                (_, None) => Err("unexpected hex digit"),
                (Some(f), Some(s)) => { v.push((f * 0x10 + s) as u8); Ok(()) }
            }
        }
    )?;
    // Check that there was no remainder
    match iter.remainder() {
        Some(_) => Err("hexstring of odd length"),
        None => Ok(v)
    }
}

/// Convert a slice of u8 to a hex string
pub fn to_hex(s: &[u8]) -> String {
    let r : Vec<String> = s.to_vec().iter().map(|b| format!("{:02x}", b)).collect();
    return r.join("");
}

pub struct BlockHeaderHash([u8; 32]);
impl_array_newtype!(BlockHeaderHash, u8, 32);
impl_array_hexstring_fmt!(BlockHeaderHash);
impl_byte_array_newtype!(BlockHeaderHash, u8, 32);
pub const BLOCK_HEADER_HASH_ENCODED_SIZE : u32 = 32;

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

/*
fn log2_floor(k: u64) -> u64 {
    if k == 0 {
        0
    }
    else {
        63u64 - (k.leading_zeros() as u64)
    }
}
*/

/// Fast extend-from-slice for bytes.  Basically, this is memcpy(3).
/// This is similar to the private append_elemnts() method in the Vec struct,
/// but slightly faster in that it requires that target already have sufficient capacity.
/// Based on https://doc.rust-lang.org/std/ptr/fn.copy_nonoverlapping.html
#[inline]
fn fast_extend_from_slice(target: &mut Vec<u8>, src: &[u8]) -> () {
    assert!(target.capacity() >= target.len() + src.len());
    let target_len = target.len();
    let src_len = src.len();
    let new_len = target_len + src_len;
    unsafe {
        let target_ptr = target.as_mut_ptr().offset(target_len as isize);
        let src_ptr = src.as_ptr();
        ptr::copy_nonoverlapping(src_ptr, target_ptr, src_len);
        target.set_len(new_len);
    }
}

pub struct TrieHash(pub [u8; 32]);
impl_array_newtype!(TrieHash, u8, 32);
impl_array_hexstring_fmt!(TrieHash);
impl_byte_array_newtype!(TrieHash, u8, 32);
pub const TRIEHASH_ENCODED_SIZE : usize = 32;

impl TrieHash {
    #[inline]
    fn from_empty_data() -> TrieHash {
        TrieHash([0xc6, 0x72, 0xb8, 0xd1, 0xef, 0x56, 0xed, 0x28, 0xab, 0x87, 0xc3, 0x62, 0x2c, 0x51, 0x14, 0x06, 0x9b, 0xdd, 0x3a, 0xd7, 0xb8, 0xf9, 0x73, 0x74, 0x98, 0xd0, 0xc0, 0x1e, 0xce, 0xf0, 0x96, 0x7a])
    }

    pub fn from_data(data: &[u8]) -> TrieHash {
        if *data == [] {
            return TrieHash::from_empty_data();
        }
        
        use sha2::Digest;
        let mut tmp = [0u8; 32];
        
        let mut sha2 = Sha512Trunc256::new();
        sha2.input(data);
        tmp.copy_from_slice(sha2.result().as_slice());

        TrieHash(tmp)
    }

    /// Human-readable hex output
    pub fn le_hex_string(&self) -> String {
        let &TrieHash(data) = self;
        let mut ret = String::with_capacity(64);
        for item in data.iter().take(32) {
            ret.push(from_digit((*item / 0x10) as u32, 16).unwrap());
            ret.push(from_digit((*item & 0x0f) as u32, 16).unwrap());
        }
        ret
    }

    /// Human-readable hex output
    pub fn be_hex_string(&self) -> String {
        let &TrieHash(data) = self;
        let mut ret = String::with_capacity(64);
        for i in (0..32).rev() {
            ret.push(from_digit((data[i] / 0x10) as u32, 16).unwrap());
            ret.push(from_digit((data[i] & 0x0f) as u32, 16).unwrap());
        }
        ret
    }
}

#[derive(Debug)]
pub enum Error {
    IOError(io::Error),
    NotFoundError,
    BackptrNotFoundError,
    ExistsError,
    BadSeekValue,
    BackPtrError,
    CorruptionError(String),
    InvalidNodeError,
    LeafError,
    ReadOnlyError,
    NotDirectoryError,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Error::IOError(ref e) => fmt::Display::fmt(e, f),
            Error::NotFoundError => f.write_str(error::Error::description(self)),
            Error::BackptrNotFoundError => f.write_str(error::Error::description(self)),
            Error::ExistsError => f.write_str(error::Error::description(self)),
            Error::BadSeekValue => f.write_str(error::Error::description(self)),
            Error::BackPtrError => f.write_str(error::Error::description(self)),
            Error::CorruptionError(ref s) => fmt::Display::fmt(s, f),
            Error::InvalidNodeError => f.write_str(error::Error::description(self)),
            Error::LeafError => f.write_str(error::Error::description(self)),
            Error::ReadOnlyError => f.write_str(error::Error::description(self)),
            Error::NotDirectoryError => f.write_str(error::Error::description(self)),
        }
    }
}

impl error::Error for Error {
    fn cause(&self) -> Option<&error::Error> {
        match *self {
            Error::IOError(ref e) => Some(e),
            Error::NotFoundError => None,
            Error::BackptrNotFoundError => None,
            Error::ExistsError => None,
            Error::BadSeekValue => None,
            Error::BackPtrError => None,
            Error::CorruptionError(ref s) => None,
            Error::InvalidNodeError => None,
            Error::LeafError => None,
            Error::ReadOnlyError => None,
            Error::NotDirectoryError => None,
        }
    }

    fn description(&self) -> &str {
        match *self {
            Error::IOError(ref e) => e.description(),
            Error::NotFoundError => "Object not found",
            Error::BackptrNotFoundError => "Object not found from backptrs",
            Error::ExistsError => "Object exists",
            Error::BadSeekValue => "Bad seek value",
            Error::BackPtrError => "Encountered a back-pointer",
            Error::CorruptionError(ref s) => s.as_str(),
            Error::InvalidNodeError => "Encountered an unexpected node",
            Error::LeafError => "Encountered an unexpected leaf",
            Error::ReadOnlyError => "Storage is in read-only mode",
            Error::NotDirectoryError => "Not a directory"
        }
    }
}

fn slice_partialeq<T: PartialEq>(s1: &[T], s2: &[T]) -> bool {
    if s1.len() != s2.len() {
        return false;
    }
    for i in 0..s1.len() {
        if s1[i] != s2[i] {
            return false;
        }
    }
    true
}

pub mod TrieNodeID {
    pub const Empty : u8 = 0;
    pub const Leaf: u8 = 1;
    pub const Node4 : u8 = 2;
    pub const Node16 : u8 = 3;
    pub const Node48 : u8 = 4;
    pub const Node256 : u8 = 5;
}

fn is_backptr(id: u8) -> bool {
    id & 0x80 != 0
}

fn set_backptr(id: u8) -> u8 {
    id | 0x80
}

fn clear_backptr(id: u8) -> u8 {
    id & 0x7f
}

pub struct TriePath([u8; 20]);
impl_array_newtype!(TriePath, u8, 20);
impl_array_hexstring_fmt!(TriePath);
impl_byte_array_newtype!(TriePath, u8, 20);

pub const TRIEPATH_MAX_LEN : usize = 20;

pub trait TrieNode {
    fn id(&self) -> u8;
    fn empty() -> Self;
    fn walk(&self, chr: u8) -> Option<TriePtr>;
    fn insert(&mut self, ptr: &TriePtr) -> bool;
    fn replace(&mut self, ptr: &TriePtr) -> bool;
    fn from_bytes<R: Read>(r: &mut R) -> Result<Self, Error>
        where Self: std::marker::Sized;
    fn to_bytes(&self, buf: &mut Vec<u8>) -> ();
    fn to_consensus_bytes(&self, &mut Vec<u8>) -> ();
    fn byte_len(&self) -> usize;
    fn ptrs(&self) -> &[TriePtr];

    // this is a way to construct a TrieNodeType from an object that implements this trait
    // DO NOT USE DIRECTLY
    fn try_as_node4(&self) -> Option<TrieNodeType>;
    fn try_as_node16(&self) -> Option<TrieNodeType>;
    fn try_as_node48(&self) -> Option<TrieNodeType>;
    fn try_as_node256(&self) -> Option<TrieNodeType>;
    fn try_as_leaf(&self) -> Option<TrieNodeType>;
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct TriePtr {
    id: u8,
    chr: u8,
    ptr: u32,
    back_block: u32,
}

pub fn ptrs_fmt(ptrs: &[TriePtr]) -> String {
    let mut strs = vec![];
    for i in 0..ptrs.len() {
        if ptrs[i].id != TrieNodeID::Empty {
            strs.push(format!("id{}chr{:02x}ptr{}bblk{}", ptrs[i].id, ptrs[i].chr, ptrs[i].ptr, ptrs[i].back_block))
        }
    }
    strs.join(",")
}

pub const TRIEPTR_SIZE : usize = 10;

impl Default for TriePtr {
    #[inline]
    fn default() -> TriePtr {
        TriePtr { id: 0, chr: 0, ptr: 0, back_block: 0 }
    }
}

impl TriePtr {
    #[inline]
    pub fn new(id: u8, chr: u8, ptr: u32) -> TriePtr {
        TriePtr {
            id: id,
            chr: chr,
            ptr: ptr,
            back_block: 0
        }
    }
    
    #[inline]
    pub fn new_backptr(id: u8, chr: u8, ptr: u32, back_block: u32) -> TriePtr {
        TriePtr {
            id: set_backptr(id),
            chr: chr,
            ptr: ptr,
            back_block: back_block
        }
    }

    #[inline]
    pub fn empty(&self) -> bool {
        self.id == 0
    }

    #[inline]
    pub fn id(&self) -> u8 {
        self.id
    }

    #[inline]
    pub fn chr(&self) -> u8 {
        self.chr
    }

    #[inline]
    pub fn ptr(&self) -> u32 {
        self.ptr
    }

    #[inline]
    pub fn back_block(&self) -> u32 {
        self.back_block
    }

    #[inline]
    pub fn from_backptr(&self) -> TriePtr {
        TriePtr {
            id: clear_backptr(self.id),
            chr: self.chr,
            ptr: self.ptr,
            back_block: 0
        }
    }

    #[inline]
    pub fn to_bytes(&self, buf: &mut Vec<u8>) -> () {
        let ptr = self.ptr();
        let back_block = self.back_block();

        let ptr_bytes = [
            self.id(),
            self.chr(),
            ((ptr & 0xff000000) >> 24) as u8,
            ((ptr & 0x00ff0000) >> 16) as u8,
            ((ptr & 0x0000ff00) >> 8) as u8,
            ((ptr & 0x000000ff)) as u8,
            ((back_block & 0xff000000) >> 24) as u8,
            ((back_block & 0x00ff0000) >> 16) as u8,
            ((back_block & 0x0000ff00) >> 8) as u8,
            ((back_block & 0x000000ff)) as u8
        ];
        fast_extend_from_slice(buf, &ptr_bytes);
    }

    #[inline]
    pub fn to_consensus_bytes(&self, buf: &mut Vec<u8>) -> () {
        // like to_bytes(), but without insertion-order
        let back_block = self.back_block();

        let consensus_ptr_bytes = [
            self.id(),
            self.chr(),
            ((back_block & 0xff000000) >> 24) as u8,
            ((back_block & 0x00ff0000) >> 16) as u8,
            ((back_block & 0x0000ff00) >> 8) as u8,
            ((back_block & 0x000000ff)) as u8
        ];

        fast_extend_from_slice(buf, &consensus_ptr_bytes);
    }

    #[inline]
    pub fn from_bytes(bytes: &[u8]) -> TriePtr {
        assert!(bytes.len() >= TRIEPTR_SIZE);
        let id = bytes[0];
        let chr = bytes[1];
        let ptr =
            (bytes[2] as u32) << 24 |
            (bytes[3] as u32) << 16 |
            (bytes[4] as u32) << 8 |
            (bytes[5] as u32);
        let back_block =
            (bytes[6] as u32) << 24 |
            (bytes[7] as u32) << 16 |
            (bytes[8] as u32) << 8 |
            (bytes[9] as u32);

        TriePtr {
            id: id,
            chr: chr,
            ptr: ptr,
            back_block: back_block
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct TrieCursor {
    path: TriePath,             // the path to walk
    index: usize,               // index into the path
    node_path_index: usize,     // index into the currently-visited node's compressed path
    nodes: Vec<TrieNodeType>,   // list of nodes this cursor visits
    node_ptrs: Vec<TriePtr>,    // list of ptr branches this cursor has taken
    block_hashes: Vec<BlockHeaderHash>,  // (optional) list of Tries we've visited.  block_hashes[i] corresponds to node_ptrs[i]
    diverged: bool
}

impl TrieCursor {
    pub fn new(path: &TriePath, root_ptr: u64) -> TrieCursor {
        TrieCursor {
            path: path.clone(),
            index: 0,
            node_path_index: 0,
            nodes: vec![],
            node_ptrs: vec![TriePtr::new(TrieNodeID::Node256, 0, root_ptr as u32)],
            block_hashes: vec![],
            diverged: false
        }
    }

    /// what point in the path are we at now?
    pub fn chr(&self) -> Option<u8> {
        if self.index > 0 && self.index <= self.path.len() {
            Some(self.path.as_bytes()[self.index-1])
        }
        else {
            None
        }
    }

    /// what offset in the path are we at?
    pub fn tell(&self) -> usize {
        self.index
    }

    /// what is the offset in the node path?
    pub fn ntell(&self) -> usize {
        self.node_path_index
    }

    /// end-of-path?
    pub fn eop(&self) -> bool {
        self.index == self.path.len()
    }

    /// diverged from path?
    pub fn div(&self) -> bool {
        self.diverged
    }

    /// last ptr pushed
    pub fn ptr(&self) -> TriePtr {
        // should always be true by construction
        assert!(self.node_ptrs.len() > 0);
        self.node_ptrs[self.node_ptrs.len()-1].clone()
    }

    /// last node visited 
    pub fn node(&self) -> Option<TrieNodeType> {
        match self.nodes.len() {
            0 => None,
            _ => Some(self.nodes[self.nodes.len()-1].clone())
        }
    }

    /// end of node path?
    pub fn eonp(&self, node: &TrieNodeType) -> bool {
        match node {
            TrieNodeType::Leaf(ref data) => self.node_path_index == data.path.len(),
            TrieNodeType::Node4(ref data) => self.node_path_index == data.path.len(),
            TrieNodeType::Node16(ref data) => self.node_path_index == data.path.len(),
            TrieNodeType::Node48(ref data) => self.node_path_index == data.path.len(),
            TrieNodeType::Node256(ref data) => self.node_path_index == data.path.len(),
        }
    }

    /// Replace the last-visited node and ptr within this trie
    fn retarget(&mut self, node: &TrieNodeType, ptr: &TriePtr, hash: &BlockHeaderHash) -> () {
        self.nodes.pop();
        self.node_ptrs.pop();
        self.block_hashes.pop();

        self.nodes.push(node.clone());
        self.node_ptrs.push(ptr.clone());
        self.block_hashes.push(hash.clone());
    }

    pub fn walk(&mut self, node: &TrieNodeType, block_hash: &BlockHeaderHash) -> Option<TriePtr> {
        test_debug!("cursor: walk: node = {:?} block = {:?}", node, block_hash);

        if self.index >= self.path.len() {
            test_debug!("cursor: out of path");
            return None;
        }

        let node_path = match node {
            TrieNodeType::Leaf(ref data) => data.path.clone(),
            TrieNodeType::Node4(ref data) => data.path.clone(),
            TrieNodeType::Node16(ref data) => data.path.clone(),
            TrieNodeType::Node48(ref data) => data.path.clone(),
            TrieNodeType::Node256(ref data) => data.path.clone(),
        };

        let path_bytes = self.path.as_bytes().clone();

        assert!(self.index + node_path.len() <= self.path.len());

        // walk this node
        self.nodes.push((*node).clone());
        self.node_path_index = 0;

        // consume as much of the partial path as we can
        for i in 0..node_path.len() {
            if node_path[i] != path_bytes[self.index] {
                // diverged
                test_debug!("cursor: diverged({:?} != {:?}): i = {}, self.index = {}, self.node_path_index = {}", &node_path, &path_bytes, i, self.index, self.node_path_index);
                self.diverged = true;
                return None;
            }
            self.index += 1;
            self.node_path_index += 1;
        }

        // walked to end of the node's path prefix.
        // Find the pointer to the next node.
        if self.index < self.path.len() {
            let chr = path_bytes[self.index];
            self.index += 1;
            let mut ptr_opt = match node {
                TrieNodeType::Node4(ref node4) => node4.walk(chr),
                TrieNodeType::Node16(ref node16) => node16.walk(chr),
                TrieNodeType::Node48(ref node48) => node48.walk(chr),
                TrieNodeType::Node256(ref node256) => node256.walk(chr),
                _ => None
            };
            
            let do_walk = match ptr_opt {
                Some(ref ptr) => {
                    if !is_backptr(ptr.id()) {
                        // already resolved
                        self.walk_backptr_finish(&ptr, block_hash);
                        true
                    }
                    else {
                        // the caller will need to follow the backptr, and call
                        // walk_backptr_step() for each node visited, and then walk_backptr_finish()
                        // once the final ptr and block_hash are discovered.
                        false
                    }
                },
                None => {
                    false
                }
            };

            if !do_walk {
                ptr_opt = None;
            }

            if ptr_opt.is_none() {
                test_debug!("cursor: not found: chr = 0x{:02x}, self.index = {}, self.path = {:?}", chr, self.index-1, &path_bytes);
            }
            ptr_opt
        }
        else {
            test_debug!("cursor: now out of path");
            None
        }
    }

    /// Record that a node was walked to by way of a backptr while walking backptrs.
    /// next_node should be the node walked to.
    /// ptr is the ptr we'll be walking from, off of next_node.
    /// block_hash is the block where next_node came from.
    pub fn walk_backptr_step_backptr(&mut self, next_node: &TrieNodeType, ptr: &TriePtr, block_hash: &BlockHeaderHash) -> () {
        let backptr = TriePtr::new(set_backptr(ptr.id()), ptr.chr(), ptr.ptr());        // set_backptr() informs update_root_hash() to skip this node
        self.node_ptrs.push(backptr);
        self.block_hashes.push(block_hash.clone());
        
        self.nodes.push(next_node.clone());
        test_debug!("Cursor: walk_backptr_step_backptr ptr={:?} block_hash={:?} next_node={:?}", ptr, block_hash, next_node);
    }
    
    /// Record that a node was alked to by way of a storage ptr while walking backptrs.
    /// ptr and block hash refer to the location of next_node.
    pub fn walk_backptr_step_node(&mut self, next_node: &TrieNodeType, ptr: &TriePtr, block_hash: &BlockHeaderHash) -> () {
        let backptr = TriePtr::new(set_backptr(ptr.id()), ptr.chr(), ptr.ptr());        // set_backptr() informs update_root_hash() to skip this node
        self.node_ptrs.push(backptr);
        self.block_hashes.push(block_hash.clone());
        
        self.nodes.push(next_node.clone());
    }

    /// Finish walking a skiplist of backptrs and record the location of the non-backptr node we landed on.
    pub fn walk_backptr_finish(&mut self, ptr: &TriePtr, block_hash: &BlockHeaderHash) -> () {
        assert!(!is_backptr(ptr.id()));

        self.node_ptrs.push(ptr.clone());
        self.block_hashes.push(block_hash.clone());
    }
}


#[derive(Clone)]
pub struct TrieLeaf {
    path: Vec<u8>,
    reserved: [u8; 40],
    backptr: TriePtr
}

impl fmt::Debug for TrieLeaf {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "TrieLeaf(path={} reserved={} backptr={:?})", &to_hex(&self.path), &to_hex(&self.reserved.to_vec()), &self.backptr)
    }
}

impl PartialEq for TrieLeaf {
    fn eq(&self, other: &TrieLeaf) -> bool {
        self.path == other.path && slice_partialeq(&self.reserved, &other.reserved) && self.backptr == other.backptr
    }
}


impl TrieLeaf {
    pub fn new(path: &Vec<u8>, data: &Vec<u8>) -> TrieLeaf {
        assert!(data.len() <= 40);
        let mut bytes = [0u8; 40];
        bytes.copy_from_slice(&data[..]);
        TrieLeaf {
            path: path.clone(),
            reserved: bytes,
            backptr: TriePtr::default()
        }
    }
}

#[derive(Clone, PartialEq)]
pub struct TrieNode4 {
    path: Vec<u8>,
    ptrs: [TriePtr; 4],
}

impl fmt::Debug for TrieNode4 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "TrieNode4(path={} ptrs={})", &to_hex(&self.path), ptrs_fmt(&self.ptrs))
    }
}

impl TrieNode4 {
    pub fn new(path: &Vec<u8>) -> TrieNode4 {
        TrieNode4 {
            path: path.clone(),
            ptrs: [TriePtr::default(); 4],
        }
    }
}

#[derive(Clone, PartialEq)]
pub struct TrieNode16 {
    path: Vec<u8>,
    ptrs: [TriePtr; 16],
}

impl fmt::Debug for TrieNode16 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "TrieNode16(path={} ptrs={})", &to_hex(&self.path), ptrs_fmt(&self.ptrs))
    }
}

impl TrieNode16 {
    pub fn new(path: &Vec<u8>) -> TrieNode16 {
        TrieNode16 {
            path: path.clone(),
            ptrs: [TriePtr::default(); 16],
        }
    }

    pub fn from_node4(node4: &TrieNode4) -> TrieNode16 {
        let mut ptrs = [TriePtr::default(); 16];
        for i in 0..4 {
            ptrs[i] = node4.ptrs[i].clone();
        }
        TrieNode16 {
            path: node4.path.clone(),
            ptrs: ptrs,
        }
    }
}

#[derive(Clone)]
pub struct TrieNode48 {
    path: Vec<u8>,
    indexes: [i8; 256],
    ptrs: [TriePtr; 48],
}

impl fmt::Debug for TrieNode48 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "TrieNode48(path={} ptrs={})", &to_hex(&self.path), ptrs_fmt(&self.ptrs))
    }
}

impl PartialEq for TrieNode48 {
    fn eq(&self, other: &TrieNode48) -> bool {
        self.path == other.path && slice_partialeq(&self.ptrs, &other.ptrs) && slice_partialeq(&self.indexes, &other.indexes)
    }
}

impl TrieNode48 {
    pub fn new(path: &Vec<u8>) -> TrieNode48 {
        TrieNode48 {
            path: path.clone(),
            indexes: [-1; 256],
            ptrs: [TriePtr::default(); 48],
        }
    }

    pub fn from_node16(node16: &TrieNode16) -> TrieNode48 {
        let mut ptrs = [TriePtr::default(); 48];
        let mut indexes = [-1i8; 256];
        for i in 0..16 {
            ptrs[i] = node16.ptrs[i].clone();
            indexes[ptrs[i].chr() as usize] = i as i8;
        }
        TrieNode48 {
            path: node16.path.clone(),
            indexes: indexes,
            ptrs: ptrs,
        }
    }
}

#[derive(Clone)]
pub struct TrieNode256 {
    path: Vec<u8>,
    ptrs: [TriePtr; 256],
}

impl fmt::Debug for TrieNode256 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "TrieNode256(path={} ptrs={})", &to_hex(&self.path), ptrs_fmt(&self.ptrs))
    }
}

impl PartialEq for TrieNode256 {
    fn eq(&self, other: &TrieNode256) -> bool {
        self.path == other.path && slice_partialeq(&self.ptrs, &other.ptrs)
    }
}

impl TrieNode256 {
    pub fn new(path: &Vec<u8>) -> TrieNode256 {
        TrieNode256 {
            path: path.clone(),
            ptrs: [TriePtr::default(); 256],
        }
    }

    pub fn from_node48(node48: &TrieNode48) -> TrieNode256 {
        let mut ptrs = [TriePtr::default(); 256];
        for i in 0..48 {
            let c = node48.ptrs[i].chr();
            ptrs[c as usize] = node48.ptrs[i].clone();
        }
        TrieNode256 {
            path: node48.path.clone(),
            ptrs: ptrs,
        }
    }
}

fn ftell<F: Seek>(f: &mut F) -> Result<u64, Error> {
    f.seek(SeekFrom::Current(0))
        .map_err(Error::IOError)
}

fn fsize<F: Seek>(f: &mut F) -> Result<u64, Error> {
    let prev = ftell(f)?;
    let res = f.seek(SeekFrom::End(0))
        .map_err(Error::IOError)?;
    f.seek(SeekFrom::Start(prev))
        .map_err(Error::IOError)?;
    Ok(res)
}

fn fseek<F: Seek>(f: &mut F, off: u64) -> Result<u64, Error> {
    f.seek(SeekFrom::Start(off))
        .map_err(Error::IOError)
}

fn fseek_end<F: Seek>(f: &mut F) -> Result<u64, Error> {
    f.seek(SeekFrom::End(0))
        .map_err(Error::IOError)
}

fn read_all<R: Read>(f: &mut R, buf: &mut [u8]) -> Result<usize, Error> {
    let mut cnt = 0;
    while cnt < buf.len() {
        let nr = f.read(&mut buf[cnt..])
            .map_err(Error::IOError)?;

        if nr == 0 {
            break;
        }

        cnt += nr;
    }
    Ok(cnt)
}

fn write_all<W: Write>(f: &mut W, buf: &[u8]) -> Result<usize, Error> {
    let mut cnt = 0;
    while cnt < buf.len() {
        let nw = f.write(&buf[cnt..buf.len()])
            .map_err(Error::IOError)?;
        cnt += nw;
    }
    Ok(cnt)
}

fn get_path_byte_len(p: &Vec<u8>) -> usize {
    let path_len_byte_len = 1;
    path_len_byte_len + p.len()
}

fn path_to_bytes(p: &Vec<u8>, buf: &mut Vec<u8>) -> () {
    // always true by construction
    assert!(p.len() < 256);
    buf.push(p.len() as u8);
    buf.append(&mut p.clone());
}

fn path_from_bytes<R: Read>(r: &mut R) -> Result<Vec<u8>, Error> {
    let mut lenbuf = [0u8; 1];
    let l_lenbuf = read_all(r, &mut lenbuf)?;

    if l_lenbuf != 1 {
        return Err(Error::CorruptionError("Could not read node path length".to_string()));
    }
    if lenbuf[0] as usize > TRIEPATH_MAX_LEN {
        test_debug!("Path length is {} (expected <= {})", lenbuf[0], TRIEPATH_MAX_LEN);
        return Err(Error::CorruptionError(format!("Node path is longer than {} bytes (got {})", TRIEPATH_MAX_LEN, lenbuf[0])));
    }

    let mut retbuf = vec![0; lenbuf[0] as usize];
    let l_retbuf = read_all(r, &mut retbuf)?;

    if l_retbuf != (lenbuf[0] as usize) {
        return Err(Error::CorruptionError(format!("Could not read full node path: only got {} out of {} bytes", l_retbuf, lenbuf[0])));
    }
    
    Ok(retbuf)
}

#[inline]
fn check_node_id(nid: u8) -> bool {
    let node_id = clear_backptr(nid);
    node_id == TrieNodeID::Leaf ||
    node_id == TrieNodeID::Node4 ||
    node_id == TrieNodeID::Node16 ||
    node_id == TrieNodeID::Node48 ||
    node_id == TrieNodeID::Node256
}

#[inline]
fn node_id_to_ptr_count(node_id: u8) -> usize {
    match clear_backptr(node_id) {
        TrieNodeID::Leaf => 1,
        TrieNodeID::Node4 => 4,
        TrieNodeID::Node16 => 16,
        TrieNodeID::Node48 => 48,
        TrieNodeID::Node256 => 256,
        _ => panic!("Unknown node ID {}", node_id)
    }
}

#[inline]
fn get_ptrs_byte_len(ptrs: &[TriePtr]) -> usize {
    let node_id_len = 1;
    node_id_len + TRIEPTR_SIZE * ptrs.len()
}

#[inline]
fn ptrs_to_bytes(node_id: u8, ptrs: &[TriePtr], buf: &mut Vec<u8>) -> () {
    assert!(check_node_id(node_id));
    assert_eq!(node_id_to_ptr_count(node_id), ptrs.len());

    buf.push(node_id);

    // faster than "for ptr in ptrs.iter()"
    let mut i = 0;
    while i < ptrs.len() {
        ptrs[i].to_bytes(buf);
        i += 1;
    }
}

#[inline]
fn ptrs_to_consensus_bytes(node_id: u8, ptrs: &[TriePtr], buf: &mut Vec<u8>) -> () {
    assert!(check_node_id(node_id));

    buf.push(node_id);
    
    // faster than "for ptr in ptrs.iter()"
    let mut i = 0;
    while i < ptrs.len() {
        ptrs[i].to_consensus_bytes(buf);
        i += 1;
    }
}

#[inline]
fn ptrs_from_bytes<R: Read>(node_id: u8, r: &mut R, ptrs_buf: &mut [TriePtr]) -> Result<u8, Error> {
    if !check_node_id(node_id) {
        test_debug!("Bad node ID {:x}", node_id);
        return Err(Error::CorruptionError(format!("Bad node ID: {:x}", node_id)));
    }

    let mut idbuf = [0u8; 1];
    let l_idbuf = read_all(r, &mut idbuf)?;

    if l_idbuf != 1 {
        test_debug!("Bad l_idbuf: {}", l_idbuf);
        return Err(Error::CorruptionError("Failed to read node ID".to_string()));
    }
    let nid = idbuf[0];

    if clear_backptr(nid) != clear_backptr(node_id) {
        test_debug!("Bad idbuf: {:x} != {:x}", nid, node_id);
        return Err(Error::CorruptionError("Failed to read expected node ID".to_string()));
    }

    let num_ptrs = node_id_to_ptr_count(node_id);
    let mut bytes = vec![0; num_ptrs * TRIEPTR_SIZE];
    let l_bytes = read_all(r, &mut bytes)?;

    if l_bytes != num_ptrs * TRIEPTR_SIZE {
        test_debug!("Bad l_bytes: {} != {}", l_bytes, num_ptrs * TRIEPTR_SIZE);
        return Err(Error::CorruptionError(format!("Failed to read node: got {} out of {} bytes", l_bytes, num_ptrs * TRIEPTR_SIZE)));
    }
    
    // not a for-loop because "for i in 0..num_ptrs" is actually kinda slow
    let mut i = 0;
    while i < num_ptrs {
        ptrs_buf[i] = TriePtr::from_bytes(&bytes[i*TRIEPTR_SIZE..(i+1)*TRIEPTR_SIZE]);
        i += 1;
    }
    Ok(nid)
}

impl TrieNode for TrieNode4 {
    fn id(&self) -> u8 {
        TrieNodeID::Node4
    }

    fn empty() -> TrieNode4 {
        TrieNode4 {
            path: vec![],
            ptrs: [TriePtr::default(); 4],
        }
    }

    fn walk(&self, chr: u8) -> Option<TriePtr> {
        for i in 0..4 {
            if self.ptrs[i].id() != TrieNodeID::Empty && self.ptrs[i].chr() == chr {
                return Some(self.ptrs[i].clone());
            }
        }
        return None;
    }

    fn to_bytes(&self, ret: &mut Vec<u8>) -> () {
        let id = self.id();
        ptrs_to_bytes(id, &self.ptrs, ret);
        path_to_bytes(&self.path, ret);
    }

    fn to_consensus_bytes(&self, ret: &mut Vec<u8>) -> () {
        let id = self.id();
        ptrs_to_consensus_bytes(id, &self.ptrs, ret);
        path_to_bytes(&self.path, ret);
    }

    fn byte_len(&self) -> usize {
        get_ptrs_byte_len(&self.ptrs) + get_path_byte_len(&self.path)
    }

    fn from_bytes<R: Read>(r: &mut R) -> Result<TrieNode4, Error> {
        let mut ptrs_slice = [TriePtr::default(); 4];
        let id = ptrs_from_bytes(TrieNodeID::Node4, r, &mut ptrs_slice)?;
        let path = path_from_bytes(r)?;

        Ok(TrieNode4 {
            path,
            ptrs: ptrs_slice,
        })
    }

    fn insert(&mut self, ptr: &TriePtr) -> bool {
        if self.replace(ptr) {
            return true;
        }

        for i in 0..4 {
            if self.ptrs[i].id() == TrieNodeID::Empty {
                self.ptrs[i] = ptr.clone();
                return true;
            }
        }
        return false;
    }

    fn replace(&mut self, ptr: &TriePtr) -> bool {
        for i in 0..4 {
            if self.ptrs[i].id() != TrieNodeID::Empty && self.ptrs[i].chr() == ptr.chr() {
                self.ptrs[i] = ptr.clone();
                return true;
            }
        }
        return false;
    }

    fn ptrs(&self) -> &[TriePtr] {
        &self.ptrs
    }

    fn try_as_node4(&self) -> Option<TrieNodeType> { Some(TrieNodeType::Node4(self.clone())) }
    fn try_as_node16(&self) -> Option<TrieNodeType> { Some(TrieNodeType::Node16(TrieNode16::from_node4(&self))) }
    fn try_as_node48(&self) -> Option<TrieNodeType> { Some(TrieNodeType::Node48(TrieNode48::from_node16(&TrieNode16::from_node4(&self)))) }
    fn try_as_node256(&self) -> Option<TrieNodeType> { Some(TrieNodeType::Node256(TrieNode256::from_node48(&TrieNode48::from_node16(&TrieNode16::from_node4(&self))))) }
    fn try_as_leaf(&self) -> Option<TrieNodeType> { None }
}

impl TrieNode for TrieNode16 {
    fn id(&self) -> u8 {
        TrieNodeID::Node16
    }

    fn empty() -> TrieNode16 {
        TrieNode16 {
            path: vec![],
            ptrs: [TriePtr::default(); 16],
        }
    }

    fn walk(&self, chr: u8) -> Option<TriePtr> {
        for i in 0..16 {
            if self.ptrs[i].id != TrieNodeID::Empty && self.ptrs[i].chr == chr {
                return Some(self.ptrs[i].clone());
            }
        }
        return None;
    }

    fn to_bytes(&self, ret: &mut Vec<u8>) -> () {
        let id = self.id();
        ptrs_to_bytes(id, &self.ptrs, ret);
        path_to_bytes(&self.path, ret);
    }

    fn to_consensus_bytes(&self, ret: &mut Vec<u8>) -> () {
        let id = self.id();
        ptrs_to_consensus_bytes(id, &self.ptrs, ret);
        path_to_bytes(&self.path, ret);
    }
    
    fn byte_len(&self) -> usize {
        get_ptrs_byte_len(&self.ptrs) + get_path_byte_len(&self.path)
    }

    fn from_bytes<R: Read>(r: &mut R) -> Result<TrieNode16, Error> {
        let mut ptrs_slice = [TriePtr::default(); 16];
        let id = ptrs_from_bytes(TrieNodeID::Node16, r, &mut ptrs_slice)?;

        let path = path_from_bytes(r)?;

        Ok(TrieNode16 {
            path, 
            ptrs: ptrs_slice,
        })
    }
    
    fn insert(&mut self, ptr: &TriePtr) -> bool {
        if self.replace(ptr) {
            return true;
        }

        for i in 0..16 {
            if self.ptrs[i].id() == TrieNodeID::Empty {
               self.ptrs[i] = ptr.clone();
               return true;
            }
        }
        return false;
    }

    fn replace(&mut self, ptr: &TriePtr) -> bool {
       for i in 0..16 {
           if self.ptrs[i].id() != TrieNodeID::Empty && self.ptrs[i].chr() == ptr.chr() {
               self.ptrs[i] = ptr.clone();
               return true;
           }
       }
       return false;
    }
    
    fn ptrs(&self) -> &[TriePtr] {
        &self.ptrs
    }
    
    fn try_as_node4(&self) -> Option<TrieNodeType> { None }
    fn try_as_node16(&self) -> Option<TrieNodeType> { Some(TrieNodeType::Node16(self.clone())) }
    fn try_as_node48(&self) -> Option<TrieNodeType> { Some(TrieNodeType::Node48(TrieNode48::from_node16(&self))) }
    fn try_as_node256(&self) -> Option<TrieNodeType> { Some(TrieNodeType::Node256(TrieNode256::from_node48(&TrieNode48::from_node16(&self)))) }
    fn try_as_leaf(&self) -> Option<TrieNodeType> { None }
}

impl TrieNode for TrieNode48 {
    fn id(&self) -> u8 {
        TrieNodeID::Node48
    }

    fn empty() -> TrieNode48 {
        TrieNode48 {
            path: vec![],
            indexes: [-1; 256],
            ptrs: [TriePtr::default(); 48],
        }
    }

    fn walk(&self, chr: u8) -> Option<TriePtr> {
        let idx = self.indexes[chr as usize];
        if idx >= 0 && idx < 48 && self.ptrs[idx as usize].id() != TrieNodeID::Empty {
            return Some(self.ptrs[idx as usize].clone());
        }
        return None;
    }

    fn to_bytes(&self, ret: &mut Vec<u8>) -> () {
        let id = self.id();
        ptrs_to_bytes(id, &self.ptrs, ret);
        ret.extend(&mut self.indexes.iter().map(|i| { let j = *i as u8; j } ));
        path_to_bytes(&self.path, ret);
    }
    
    fn to_consensus_bytes(&self, ret: &mut Vec<u8>) -> () {
        let id = self.id();
        ptrs_to_consensus_bytes(id, &self.ptrs, ret);
        ret.extend(&mut self.indexes.iter().map(|i| { let j = *i as u8; j } ));
        path_to_bytes(&self.path, ret);
    }
    
    fn byte_len(&self) -> usize {
        get_ptrs_byte_len(&self.ptrs) + 256 + get_path_byte_len(&self.path)
    }

    fn from_bytes<R: Read>(r: &mut R) -> Result<TrieNode48, Error> {
        let mut ptrs_slice = [TriePtr::default(); 48];
        let id = ptrs_from_bytes(TrieNodeID::Node48, r, &mut ptrs_slice)?;
        
        let mut indexes = [0u8; 256];
        let l_indexes = r.read(&mut indexes)
            .map_err(Error::IOError)?;
       
        if l_indexes != 256 {
            return Err(Error::CorruptionError("Node48: Failed to read 256 indexes".to_string()));
        }

        let path = path_from_bytes(r)?;

        let indexes_i8 : Vec<i8> = indexes.iter().map(|i| { let j = *i as i8; j } ).collect();
        let mut indexes_slice = [0i8; 256];
        indexes_slice.copy_from_slice(&indexes_i8[..]);

        // not a for-loop because "for ptr in ptrs_slice.iter()" is actually kinda slow
        let mut i = 0;
        while i < ptrs_slice.len() {
            let ptr = &ptrs_slice[i];
            if !(ptr.id() == TrieNodeID::Empty || (indexes_slice[ptr.chr() as usize] >= 0 && indexes_slice[ptr.chr() as usize] < 48)) {
                return Err(Error::CorruptionError("Node48: corrupt index array: invalid index value".to_string()));
            }
            i += 1;
        }

        // not a for-loop because "for i in 0..256" is actually kinda slow
        i = 0;
        while i < 256 {
            if !(indexes_slice[i] < 0 || (indexes_slice[i] >= 0 && (indexes_slice[i] as usize) < ptrs_slice.len() && ptrs_slice[indexes_slice[i] as usize].id() != TrieNodeID::Empty)) {
                return Err(Error::CorruptionError("Node48: corrupt index array: index points to empty node".to_string()));
            }
            i += 1;
        }

        Ok(TrieNode48 {
            path,
            indexes: indexes_slice,
            ptrs: ptrs_slice,
        })
    }

    fn insert(&mut self, ptr: &TriePtr) -> bool {
        if self.replace(ptr) {
            return true;
        }

        let c = ptr.chr();
        for i in 0..48 {
            if self.ptrs[i].id() == TrieNodeID::Empty {
                self.indexes[c as usize] = i as i8;
                self.ptrs[i] = ptr.clone();
                return true;
            }
        }
        return false;
    }

    fn replace(&mut self, ptr: &TriePtr) -> bool {
        let i = self.indexes[ptr.chr() as usize];
        if i >= 0 {
            self.ptrs[i as usize] = ptr.clone();
            return true;
        }
        else {
            return false;
        }
    }
    
    fn ptrs(&self) -> &[TriePtr] {
        &self.ptrs
    }
    
    fn try_as_node4(&self) -> Option<TrieNodeType> { None }
    fn try_as_node16(&self) -> Option<TrieNodeType> { None }
    fn try_as_node48(&self) -> Option<TrieNodeType> { Some(TrieNodeType::Node48(self.clone())) }
    fn try_as_node256(&self) -> Option<TrieNodeType> { Some(TrieNodeType::Node256(TrieNode256::from_node48(self))) }
    fn try_as_leaf(&self) -> Option<TrieNodeType> { None }
}

impl TrieNode for TrieNode256 {
    fn id(&self) -> u8 {
        TrieNodeID::Node256
    }

    fn empty() -> TrieNode256 {
        TrieNode256 {
            path: vec![],
            ptrs: [TriePtr::default(); 256],
        }
    }

    fn walk(&self, chr: u8) -> Option<TriePtr> {
        if self.ptrs[chr as usize].id() != TrieNodeID::Empty {
            return Some(self.ptrs[chr as usize].clone());
        }
        return None;
    }

    fn to_bytes(&self, ret: &mut Vec<u8>) -> () {
        let id = self.id();
        ptrs_to_bytes(id, &self.ptrs, ret);
        path_to_bytes(&self.path, ret);
    }

    fn to_consensus_bytes(&self, ret: &mut Vec<u8>) -> () {
        let id = self.id();
        ptrs_to_consensus_bytes(id, &self.ptrs, ret);
        path_to_bytes(&self.path, ret);
    }
    
    fn byte_len(&self) -> usize {
        get_ptrs_byte_len(&self.ptrs) + get_path_byte_len(&self.path)
    }

    fn from_bytes<R: Read>(r: &mut R) -> Result<TrieNode256, Error> {
        let mut ptrs_slice = [TriePtr::default(); 256];
        let id = ptrs_from_bytes(TrieNodeID::Node256, r, &mut ptrs_slice)?;

        let path = path_from_bytes(r)?;
        
        Ok(TrieNode256 {
            path, 
            ptrs: ptrs_slice,
        })
    }

    fn insert(&mut self, ptr: &TriePtr) -> bool {
        if self.replace(ptr) {
            return true;
        }
        let c = ptr.chr() as usize;
        self.ptrs[c] = ptr.clone();
        return true;
    }

    fn replace(&mut self, ptr: &TriePtr) -> bool {
        let c = ptr.chr() as usize;
        if self.ptrs[c].id() != TrieNodeID::Empty && self.ptrs[c].chr() == ptr.chr() {
            self.ptrs[c] = ptr.clone();
            return true;
        }
        else {
            return false;
        }
    }
    
    fn ptrs(&self) -> &[TriePtr] {
        &self.ptrs
    }
    
    fn try_as_node4(&self) -> Option<TrieNodeType> { None }
    fn try_as_node16(&self) -> Option<TrieNodeType> { None }
    fn try_as_node48(&self) -> Option<TrieNodeType> { None }
    fn try_as_node256(&self) -> Option<TrieNodeType> { Some(TrieNodeType::Node256(self.clone())) }
    fn try_as_leaf(&self) -> Option<TrieNodeType> { None }
}

impl TrieNode for TrieLeaf {
    fn id(&self) -> u8 {
        TrieNodeID::Leaf
    }

    fn empty() -> TrieLeaf {
        TrieLeaf::new(&vec![], &[0u8; 40].to_vec())
    }

    fn walk(&self, _chr: u8) -> Option<TriePtr> {
        None
    }

    fn to_bytes(&self, ret: &mut Vec<u8>) -> () {
        let id = self.id();
        ret.push(id);
        path_to_bytes(&self.path, ret);
        // ret.extend_from_slice(&self.reserved);
        fast_extend_from_slice(ret, &self.reserved);
        ptrs_to_bytes(id, &[self.backptr], ret);
    }

    fn to_consensus_bytes(&self, buf: &mut Vec<u8>) -> () {
        self.to_bytes(buf)
    }
    
    fn byte_len(&self) -> usize {
        1 + get_path_byte_len(&self.path) + self.reserved.len() + get_ptrs_byte_len(&[self.backptr])
    }

    fn from_bytes<R: Read>(r: &mut R) -> Result<TrieLeaf, Error> {
        let mut idbuf = [0u8; 1];
        let l_idbuf = r.read(&mut idbuf)
            .map_err(Error::IOError)?;

        if l_idbuf != 1 {
            return Err(Error::CorruptionError("Leaf: failed to read ID".to_string()));
        }

        if clear_backptr(idbuf[0]) != TrieNodeID::Leaf {
            return Err(Error::CorruptionError(format!("Leaf: bad ID {:x}", idbuf[0])));
        }

        let path = path_from_bytes(r)?;
        let mut reserved = [0u8; 40];
        let l_reserved = r.read(&mut reserved)
            .map_err(Error::IOError)?;

        if l_reserved != 40 {
            return Err(Error::CorruptionError(format!("Leaf: read only {} out of {} bytes", l_reserved, 40)));
        }
        
        let mut ptrs_slice = [TriePtr::default(); 1];
        ptrs_from_bytes(TrieNodeID::Leaf, r, &mut ptrs_slice)?;

        Ok(TrieLeaf {
            path: path,
            reserved: reserved,
            backptr: ptrs_slice[0]
        })
    }

    fn insert(&mut self, _ptr: &TriePtr) -> bool {
        panic!("can't insert into a leaf");
    }

    fn replace(&mut self, _ptr: &TriePtr) -> bool {
        panic!("can't replace in a leaf");
    }
    
    fn ptrs(&self) -> &[TriePtr] {
        &[]
    }
    
    fn try_as_node4(&self) -> Option<TrieNodeType> { None }
    fn try_as_node16(&self) -> Option<TrieNodeType> { None }
    fn try_as_node48(&self) -> Option<TrieNodeType> { None }
    fn try_as_node256(&self) -> Option<TrieNodeType> { None }
    fn try_as_leaf(&self) -> Option<TrieNodeType> { Some(TrieNodeType::Leaf(self.clone())) }
}

#[derive(Debug, Clone, PartialEq)]
pub enum TrieNodeType {
    Node4(TrieNode4),
    Node16(TrieNode16),
    Node48(TrieNode48),
    Node256(TrieNode256),
    Leaf(TrieLeaf),
}

/// hash this node and its childrens' hashes
/// (put outside the trie since an storage type isn't needed)
fn get_node_hash<T: TrieNode + std::fmt::Debug>(node: &T, child_hashes: &Vec<TrieHash>) -> TrieHash {
    let mut sha2 = Sha512Trunc256::new();
    let mut buf = Vec::with_capacity(node.byte_len());

    node.to_consensus_bytes(&mut buf);
    sha2.input(&buf);
    for child_hash in child_hashes {
        sha2.input(&child_hash.as_bytes());
    }
    
    let mut res = [0u8; 32];
    res.copy_from_slice(sha2.result().as_slice());

    let ret = TrieHash(res);
    test_debug!("get_node_hash: hash {:?} = {:?} + {:?}", &ret, node, child_hashes);
    ret
}

/// hash this node and its childrens' hashes, represented as a byte vector
/// (put outside the trie since an S-type isn't needed)
fn get_node_hash_bytes<T: TrieNode + std::fmt::Debug>(node: &T, child_hash_bytes: &Vec<u8>) -> TrieHash {
    assert_eq!(child_hash_bytes.len() % TRIEHASH_ENCODED_SIZE, 0);

    let mut sha2 = Sha512Trunc256::new();
    let mut buf = Vec::with_capacity(node.byte_len());

    node.to_consensus_bytes(&mut buf);
    sha2.input(&buf);
    sha2.input(child_hash_bytes);
    
    let mut res = [0u8; 32];
    res.copy_from_slice(sha2.result().as_slice());

    let ret = TrieHash(res);

    if child_hash_bytes.len() >= 50 {
        // extract individual hashes
        let mut all_hashes = Vec::with_capacity(child_hash_bytes.len() / TRIEHASH_ENCODED_SIZE);
        for i in 0..child_hash_bytes.len() / TRIEHASH_ENCODED_SIZE {
            let mut h_slice = [0u8; TRIEHASH_ENCODED_SIZE];
            h_slice.copy_from_slice(&child_hash_bytes[TRIEHASH_ENCODED_SIZE*i..TRIEHASH_ENCODED_SIZE*(i+1)]);
            all_hashes.push(TrieHash(h_slice))
        }
        test_debug!("get_node_hash_bytes: hash {:?} = {:?} + {:?}... ({})", &ret, node, &all_hashes, child_hash_bytes.len());
    }
    else {
        test_debug!("get_node_hash_bytes: hash {:?} = {:?} + {:?}... ({})", &ret, node, &child_hash_bytes, child_hash_bytes.len());
    }

    ret
}

fn _read_hash_bytes<F: Read + Write + Seek>(f: &mut F, buf: &mut Vec<u8>) -> Result<(), Error> {
    let mut hashbytes = [0u8; 32];
    f.read(&mut hashbytes)
        .map_err(Error::IOError)?;
    // buf.extend_from_slice(&hashbytes);
    fast_extend_from_slice(buf, &hashbytes);
    Ok(())
}

fn read_node_hash_bytes<F: Read + Write + Seek>(f: &mut F, ptr: &TriePtr, buf: &mut Vec<u8>) -> Result<(), Error> {
    fseek(f, ptr.ptr() as u64)?;
    _read_hash_bytes(f, buf)
}
    
fn count_children(children: &[TriePtr]) -> usize {
    let mut cnt = 0;
    for i in 0..children.len() {
        if children[i].id() != TrieNodeID::Empty {
            cnt += 1;
        }
    }
    cnt
}

/// Node wire format:
/// 0               32 33               33+X         33+X+Y
/// |---------------|--|------------------|-----------|
///   node hash      id  ptrs & ptr data      path
///
/// X is fixed and determined by the TrieNodeType variant.
/// Y is variable, but no more than TriePath::len()
fn read_nodetype<F: Read + Write + Seek>(f: &mut F, ptr: &TriePtr) -> Result<(TrieNodeType, TrieHash), Error> {
    test_debug!("read_nodetype at {:?}", ptr);
    let mut h_bytes = Vec::with_capacity(TRIEHASH_ENCODED_SIZE);
    read_node_hash_bytes(f, ptr, &mut h_bytes)?;

    let node = match ptr.id() {
        TrieNodeID::Node4 => {
            let node = TrieNode4::from_bytes(f)?;
            TrieNodeType::Node4(node)
        },
        TrieNodeID::Node16 => {
            let node = TrieNode16::from_bytes(f)?;
            TrieNodeType::Node16(node)
        },
        TrieNodeID::Node48 => {
            let node = TrieNode48::from_bytes(f)?;
            TrieNodeType::Node48(node)
        },
        TrieNodeID::Node256 => {
            let node = TrieNode256::from_bytes(f)?;
            TrieNodeType::Node256(node)
        },
        TrieNodeID::Leaf => {
            let node = TrieLeaf::from_bytes(f)?;
            TrieNodeType::Leaf(node)
        },
        _ => {
            return Err(Error::CorruptionError(format!("read_node_type: Unknown trie node type {}", ptr.id())));
        }
    };

    let mut h = [0u8; 32];
    h.copy_from_slice(&h_bytes[0..32]);
    Ok((node, TrieHash(h)))
}

/// calculate how big a node will be, including its hash 
fn get_node_byte_len(node: &TrieNodeType) -> usize {
    let hash_len = TRIEHASH_ENCODED_SIZE;
    let node_byte_len = match node {
        TrieNodeType::Leaf(ref data) => data.byte_len(),
        TrieNodeType::Node4(ref data) => data.byte_len(),
        TrieNodeType::Node16(ref data) => data.byte_len(),
        TrieNodeType::Node48(ref data) => data.byte_len(),
        TrieNodeType::Node256(ref data) => data.byte_len()
    };
    hash_len + node_byte_len
}

/// write all the bytes for a node, including its hash
fn write_node_bytes<F: Read + Write + Seek, T: TrieNode + std::fmt::Debug>(f: &mut F, node: &T, hash: TrieHash) -> Result<usize, Error> {
    let mut bytes = Vec::with_capacity(node.byte_len() + TRIEHASH_ENCODED_SIZE);
    // bytes.extend_from_slice(hash.as_bytes());
    fast_extend_from_slice(&mut bytes, hash.as_bytes());
    node.to_bytes(&mut bytes);
    
    assert_eq!(bytes.len(), node.byte_len() + TRIEHASH_ENCODED_SIZE);

    let ptr = ftell(f)?;
    test_debug!("write_node: {:?} {:?} at {}-{}", node, &hash, ptr, ptr + bytes.len() as u64);

    write_all(f, &bytes[..])
}

pub trait TrieStorage {
    fn extend(&mut self, bhh: &BlockHeaderHash) -> Result<(), Error>;
    fn open(&mut self, bhh: &BlockHeaderHash, readwrite: bool) -> Result<(), Error>;
    fn tell(&self) -> BlockHeaderHash;
    fn root_ptr(&self) -> u64;
    fn block_walk(&self, back_block: u32) -> Result<BlockHeaderHash, Error>;
    fn readwrite(&self) -> bool;
    fn format(&mut self) -> Result<(), Error>;
    fn read_node_hash_bytes(&mut self, ptr: &TriePtr, buf: &mut Vec<u8>) -> Result<(), Error>;
    fn read_node(&mut self, ptr: &TriePtr) -> Result<(TrieNodeType, TrieHash), Error>;
    fn write_node(&mut self, node: &TrieNodeType, hash: TrieHash) -> Result<(), Error>;
    fn flush(&mut self) -> Result<(), Error>;
    fn num_blocks(&self) -> usize;
}


pub struct TrieRAM {
    data: Vec<(TrieNodeType, TrieHash)>,
    offset: u64,
    num_nodes: u64,
    block_header: BlockHeaderHash,
    readonly: bool,

    read_count: u64,
    read_backptr_count: u64,
    read_node_count: u64,
    read_leaf_count: u64,

    write_count: u64,
    write_backptr_count: u64,
    write_node_count: u64,
    write_leaf_count: u64,

    total_bytes: usize
}

// Trie in RAM without the serialization overhead
impl TrieRAM {
    pub fn new(block_header: &BlockHeaderHash, capacity_hint: usize) -> TrieRAM {
        TrieRAM {
            data: Vec::with_capacity(capacity_hint),
            offset: 0,
            num_nodes: 0,
            block_header: block_header.clone(),
            readonly: false,

            read_count: 0,
            read_backptr_count: 0,
            read_node_count: 0,
            read_leaf_count: 0,

            write_count: 0,
            write_backptr_count: 0,
            write_node_count: 0,
            write_leaf_count: 0,

            total_bytes: 0
        }
    }
    
    pub fn stats(&mut self) -> (u64, u64) {
        let r = self.read_count;
        let w = self.write_count;
        self.read_count = 0;
        self.write_count = 0;
        (r, w)
    }

    pub fn node_stats(&mut self) -> (u64, u64, u64, u64) {
        let nr = self.read_node_count;
        let br = self.read_backptr_count;
        let nw = self.write_node_count;
        let bw = self.write_backptr_count;

        self.read_node_count = 0;
        self.read_backptr_count = 0;
        self.write_node_count = 0;
        self.write_backptr_count = 0;
            
        (nr, br, nw, bw)
    }

    pub fn leaf_stats(&mut self) -> (u64, u64) {
        let lr = self.read_leaf_count;
        let lw = self.write_leaf_count;

        self.read_leaf_count = 0;
        self.write_leaf_count = 0;

        (lr, lw)
    }

    fn dump_traverse<F: Read + Write + Seek>(&mut self, f: &mut F, root: &TrieNodeType, hash: &TrieHash, parent_hash: &BlockHeaderHash) -> Result<u64, Error> {
        let mut frontier : VecDeque<(TrieNodeType, TrieHash)> = VecDeque::new();

        let mut node_data = vec![];
        let mut offsets = vec![];

        frontier.push_back((root.clone(), hash.clone()));

        let mut ptr = BLOCK_HEADER_HASH_ENCODED_SIZE as u64;       // first 32 bytes is reserved for the parent block hash
        
        // step 1: write out each node in breadth-first order to get their ptr offsets
        while frontier.len() > 0 {
            let (node, node_hash) = match frontier.pop_front() {
                Some((n, h)) => (n, h),
                None => {
                    break;
                }
            };

            // calculate size
            let num_written = get_node_byte_len(&node);
            ptr += num_written as u64;
            
            // queue each child
            match node {
                TrieNodeType::Leaf(_) => {},
                TrieNodeType::Node4(ref data) => {
                    for i in 0..4 {
                        if data.ptrs[i].id != TrieNodeID::Empty && !is_backptr(data.ptrs[i].id) {
                            let (child, child_hash) = self.read_node(&data.ptrs[i])?;
                            frontier.push_back((child, child_hash));
                        }
                    }
                },
                TrieNodeType::Node16(ref data) => {
                    for i in 0..16 {
                        if data.ptrs[i].id != TrieNodeID::Empty && !is_backptr(data.ptrs[i].id) {
                            let (child, child_hash) = self.read_node(&data.ptrs[i])?;
                            frontier.push_back((child, child_hash));
                        }
                    }
                },
                TrieNodeType::Node48(ref data) => {
                    for i in 0..48 {
                        if data.ptrs[i].id != TrieNodeID::Empty && !is_backptr(data.ptrs[i].id) {
                            let (child, child_hash) = self.read_node(&data.ptrs[i])?;
                            frontier.push_back((child, child_hash));
                        }
                    }
                },
                TrieNodeType::Node256(ref data) => {
                    for i in 0..256 {
                        if data.ptrs[i].id != TrieNodeID::Empty && !is_backptr(data.ptrs[i].id) {
                            let (child, child_hash) = self.read_node(&data.ptrs[i])?;
                            frontier.push_back((child, child_hash));
                        }
                    }
                },
            }
            
            node_data.push((node, node_hash));
            offsets.push(ptr as u32);
        }

        assert_eq!(offsets.len(), node_data.len());

        // step 2: update ptrs in all nodes
        let mut i = 0;
        for j in 0..node_data.len() {
            match node_data[j].0 {
                TrieNodeType::Leaf(_) => {},
                TrieNodeType::Node4(ref mut data) => {
                    for k in 0..4 {
                        if data.ptrs[k].id != TrieNodeID::Empty && !is_backptr(data.ptrs[k].id) {
                            data.ptrs[k].ptr = offsets[i];
                            i += 1;
                        }
                    }
                },
                TrieNodeType::Node16(ref mut data) => {
                    for k in 0..16 {
                        if data.ptrs[k].id != TrieNodeID::Empty && !is_backptr(data.ptrs[k].id) {
                            data.ptrs[k].ptr = offsets[i];
                            i += 1;
                        }
                    }
                },
                TrieNodeType::Node48(ref mut data) => {
                    for k in 0..48 {
                        if data.ptrs[k].id != TrieNodeID::Empty && !is_backptr(data.ptrs[k].id) {
                            data.ptrs[k].ptr = offsets[i];
                            i += 1;
                        }
                    }
                },
                TrieNodeType::Node256(ref mut data) => {
                    for k in 0..256 {
                        if data.ptrs[k].id != TrieNodeID::Empty && !is_backptr(data.ptrs[k].id) {
                            data.ptrs[k].ptr = offsets[i];
                            i += 1;
                        }
                    }
                }
            }
        }

        // step 3: write out each node (now that they have the write ptrs)
        frontier.push_back((root.clone(), hash.clone()));

        // write parent block ptr
        fseek(f, 0)?;
        write_all(f, parent_hash.as_bytes())?;

        for i in 0..node_data.len() {
            // dump the node to storage
            let node_hash = node_data[i].1;
            let _ = match node_data[i].0 {
                TrieNodeType::Leaf(ref data) => write_node_bytes(f, data, node_hash),
                TrieNodeType::Node4(ref data) => write_node_bytes(f, data, node_hash),
                TrieNodeType::Node16(ref data) => write_node_bytes(f, data, node_hash),
                TrieNodeType::Node48(ref data) => write_node_bytes(f, data, node_hash),
                TrieNodeType::Node256(ref data) => write_node_bytes(f, data, node_hash),
            }?;
            
            // next node
            fseek(f, offsets[i] as u64)?;
        }

        Ok(ptr)
    }

    pub fn dump<F: Read + Write + Seek>(&mut self, f: &mut F, bhh: &BlockHeaderHash, parent_bhh: &BlockHeaderHash) -> Result<u64, Error> {
        if self.block_header == *bhh {
            let root_ptr = self.root_ptr();
            let (root, hash) = self.read_node(&TriePtr::new(TrieNodeID::Node256, 0, root_ptr as u32))?;
            self.dump_traverse(f, &root, &hash, parent_bhh)
        }
        else {
            test_debug!("Failed to dump {:?}: not the current block", bhh);
            Err(Error::NotFoundError)
        }
    }

    fn size_hint(&self) -> usize {
        self.total_bytes
    }
}

impl TrieStorage for TrieRAM {
    fn extend(&mut self, bhh: &BlockHeaderHash) -> Result<(), Error> {
        if self.block_header == *bhh {
            return Err(Error::ExistsError);
        }
        test_debug!("Extend to {:?}", bhh);
        self.block_header = bhh.clone();
        self.offset = 0;
        self.num_nodes = 0;
        self.data.clear();
        self.readonly = false;
        Ok(())
    }

    fn open(&mut self, bhh: &BlockHeaderHash, readwrite: bool) -> Result<(), Error> {
        if self.block_header != *bhh {
            test_debug!("Failed to open {:?}: not the current block", bhh);
            return Err(Error::NotFoundError);
        }
        self.block_header = bhh.clone();
        self.offset = 0;
        self.num_nodes = self.data.len() as u64;
        self.readonly = !readwrite;
        Ok(())
    }

    fn tell(&self) -> BlockHeaderHash {
        self.block_header.clone()
    }
    
    fn block_walk(&self, back_block: u32) -> Result<BlockHeaderHash, Error> {
        panic!("Not implemented for TrieRAM");
    }

    fn root_ptr(&self) -> u64 { 0 }

    fn readwrite(&self) -> bool {
        !self.readonly
    }

    fn format(&mut self) -> Result<(), Error> {
        if self.readonly {
            test_debug!("Read-only!");
            return Err(Error::ReadOnlyError);
        }

        self.data.clear();
        self.offset = 0;
        self.num_nodes = 0;
        Ok(())
    }

    fn read_node_hash_bytes(&mut self, ptr: &TriePtr, buf: &mut Vec<u8>) -> Result<(), Error> {
        if (ptr.ptr() as u64) >= (self.data.len() as u64) {
            test_debug!("TrieRAM: Failed to read node bytes: {} >= {}", ptr.ptr(), self.data.len());
            Err(Error::NotFoundError)
        }
        else {
            // buf.extend_from_slice(self.data[ptr.ptr() as usize].1.as_bytes());
            fast_extend_from_slice(buf, self.data[ptr.ptr() as usize].1.as_bytes());
            Ok(())
        }
    }

    fn read_node(&mut self, ptr: &TriePtr) -> Result<(TrieNodeType, TrieHash), Error> {
        let disk_ptr = ftell(self)?;
        test_debug!("TrieRAM: read_node({:?}): at {}: {:?}", &self.block_header, disk_ptr, ptr);

        self.read_count += 1;
        if is_backptr(ptr.id()) {
            self.read_backptr_count += 1;
        }
        else if ptr.id() == TrieNodeID::Leaf {
            self.read_leaf_count += 1;
        }
        else {
            self.read_node_count += 1;
        }

        if (ptr.ptr() as u64) >= (self.data.len() as u64) {
            test_debug!("TrieRAM: Failed to read node: {} >= {}", ptr.ptr(), self.data.len());
            Err(Error::NotFoundError)
        }
        else {
            Ok(self.data[ptr.ptr() as usize].clone())
        }
    }

    fn write_node(&mut self, node: &TrieNodeType, hash: TrieHash) -> Result<(), Error> {
        if self.readonly {
            test_debug!("Read-only!");
            return Err(Error::ReadOnlyError);
        }

        let disk_ptr = ftell(self)?;
        test_debug!("TrieRAM: write_node({:?}): at {}: {:?} {:?}", &self.block_header, disk_ptr, &hash, node);
        
        self.write_count += 1;
        match node {
            TrieNodeType::Leaf(ref data) => {
                self.write_leaf_count += 1;
            },
            _ => {
                self.write_node_count += 1;
            }
        }

        if self.offset < (self.data.len() as u64) {
            self.data[self.offset as usize] = (node.clone(), hash);
            self.offset += 1;
            Ok(())
        }
        else if self.offset == (self.data.len() as u64) {
            self.data.push((node.clone(), hash));
            self.offset += 1;
            self.num_nodes += 1;
            self.total_bytes += get_node_byte_len(node);
            Ok(())
        }
        else {
            test_debug!("Failed to write node bytes: off the end of the buffer");
            Err(Error::NotFoundError)
        }
    }

    fn flush(&mut self) -> Result<(), Error> {
        Ok(())
    }

    fn num_blocks(&self) -> usize {
        1
    }
}

impl Seek for TrieRAM {
    fn seek(&mut self, pos: SeekFrom) -> io::Result<u64> {
        match pos {
            SeekFrom::Start(ref loc) => {
                let prev = self.offset;
                self.offset = *loc;
                Ok(prev)
            },
            SeekFrom::End(ref loc) => {
                let prev = self.num_nodes;
                let abs_loc = (*loc).abs() as u64;
                if abs_loc > self.num_nodes {
                    // can't seek behind 0
                    return Err(io::Error::new(io::ErrorKind::InvalidInput, Error::BadSeekValue));
                }

                let new_offset = (self.num_nodes as i128) + (*loc as i128);
                if new_offset > ((1 as i128) << 64) - 1 {
                    // overflow 
                    return Err(io::Error::new(io::ErrorKind::InvalidInput, Error::BadSeekValue));
                }

                self.offset = new_offset as u64;
                Ok(prev)
            },
            SeekFrom::Current(ref loc) => {
                let prev = self.offset;
                let abs_loc = (*loc).abs() as u64;
                if abs_loc > self.num_nodes {
                    // can't seek behind 0
                    return Err(io::Error::new(io::ErrorKind::InvalidInput, Error::BadSeekValue));
                }

                let new_offset = (self.offset as i128) + (*loc as i128);
                if new_offset > ((1 as i128) << 64) - 1 {
                    // overflow 
                    return Err(io::Error::new(io::ErrorKind::InvalidInput, Error::BadSeekValue));
                }

                self.offset = new_offset as u64;
                Ok(prev)
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct TrieForkPtr {
    fork_id: usize,
    index: usize,
    parent_fork_id: usize,
    parent_index: usize
}

impl TrieForkPtr {
    pub fn new(fork_id: usize, index: usize, parent_fork_id: usize, parent_index: usize) -> TrieForkPtr {
        TrieForkPtr {
            fork_id,
            index,
            parent_fork_id,
            parent_index
        }
    }
}

// fork table for the disk-backed trie
#[derive(Debug, Clone, PartialEq)]
pub struct TrieForkTable {
    // map fork segments
    fork_table: Vec<Vec<BlockHeaderHash>>,

    // map each block header hash to its fork ID, the length of the fork ID column at the time
    // of insertion (helps speed up walking backwards), and the parent fork ID
    fork_ids: HashMap<BlockHeaderHash, TrieForkPtr>
}

impl TrieForkTable {
    pub fn new(root_hash: &BlockHeaderHash, parent_children: &HashMap<BlockHeaderHash, Vec<BlockHeaderHash>>) -> Result<TrieForkTable, Error> {
        // extend out to all children
        let mut fork_table = TrieForkTable {
            fork_table: vec![],
            fork_ids: HashMap::new()
        };

        let mut fork_queue = VecDeque::new();
        fork_queue.push_back(root_hash.clone());

        while fork_queue.len() > 0 {
            let next_hash = match fork_queue.pop_front() {
                Some(h) => {
                    h
                },
                None => {
                    break;
                }
            };

            match parent_children.get(&next_hash) {
                Some(children) => {
                    // ensure that fork table columns are all created in the same order
                    let mut sorted_children = children.clone();
                    sorted_children.sort();

                    for child in sorted_children.iter() {
                        fork_table.extend(&next_hash, child)?;
                        fork_queue.push_back(child.clone());
                    }
                },
                None => {}
            }
        }

        Ok(fork_table)
    }

    pub fn extend(&mut self, cur_block: &BlockHeaderHash, next_block: &BlockHeaderHash) -> Result<(), Error> {
        if !self.fork_ids.contains_key(cur_block) {
            if self.fork_ids.len() == 0 && self.fork_table.len() == 0 {
                // first block -- add cur_block as the parent of next_block as the first fork column
                self.fork_table.push(vec![cur_block.clone(), next_block.clone()]);

                let cur_fork_ptr = TrieForkPtr::new(0, 0, 0, 0);
                let next_fork_ptr = TrieForkPtr::new(0, 1, 0, 0);

                test_debug!("New fork table: cur = {:?}, next = {:?}", cur_block, next_block);
                self.fork_ids.insert(cur_block.clone(), cur_fork_ptr);
                self.fork_ids.insert(next_block.clone(), next_fork_ptr);
                return Ok(());
            }
            else {
                test_debug!("No fork ID for {:?}", cur_block);
                return Err(Error::NotFoundError);
            }
        }

        let fork_id = match self.fork_ids.get(cur_block) {
            Some(ref fork_ptr) => {
                fork_ptr.fork_id
            },
            None => {
                unreachable!();
            }
        };

        if self.fork_table[fork_id][self.fork_table[fork_id].len() - 1] == *cur_block {

            // appending to this fork
            self.fork_table[fork_id].push((*next_block).clone());

            let fork_ptr = TrieForkPtr::new(fork_id, self.fork_table[fork_id].len() - 1, fork_id, self.fork_table[fork_id].len() - 2);
            self.fork_ids.insert((*next_block).clone(), fork_ptr.clone());
            
            test_debug!("Append {:?} to fork {} off of {:?} at {:?}", next_block, fork_id, cur_block, &fork_ptr);
        }
        else {
            // starting a new fork column
            self.fork_table.push(vec![(*next_block).clone()]);
            
            // what's the index in cur_block's fork column of cur_block?
            let cur_block_fork_ptr = match self.fork_ids.get(cur_block) {
                Some(fork_ptr) => {
                    fork_ptr.clone()
                },
                None => {
                    return Err(Error::CorruptionError(format!("No fork ptr for {:?}", cur_block)));
                }
            };

            assert_eq!(cur_block_fork_ptr.fork_id, fork_id);

            let next_fork_id = self.fork_table.len() - 1;
            let fork_ptr = TrieForkPtr::new(next_fork_id, 0, fork_id, cur_block_fork_ptr.index);
            self.fork_ids.insert((*next_block).clone(), fork_ptr.clone());
            
            test_debug!("Start a new fork column for {:?} at fork column {}, off of {:?} in fork column {} index {}", next_block, next_fork_id, cur_block, fork_ptr.parent_fork_id, fork_ptr.parent_index);
        }

        Ok(())
    }

    pub fn walk_back(&self, cur_block: &BlockHeaderHash, _back_block: u32) -> Result<BlockHeaderHash, Error> {
        let back_block = _back_block as usize;
        if back_block == 0 {
            return Ok(cur_block.clone());
        }
        let mut cnt = 0;

        // are we staying within our own fork column?
        let (fork_id, index) = match self.fork_ids.get(cur_block) {
            Some(ref fork_ptr) => {
                (fork_ptr.fork_id, fork_ptr.index)
            },
            None => {
                test_debug!("Not in fork table: {:?}", cur_block);
                return Err(Error::NotFoundError);
            }
        };

        if back_block <= index {
            test_debug!("Found in our own fork column {}: at {} - {}", fork_id, index, back_block);
            return Ok(self.fork_table[fork_id][index - back_block].clone());
        }

        // target is in some other fork column.
        // walk from the end of this fork column.
        cnt += index + 1;
        let mut block_ptr = self.fork_table[fork_id][0].clone();

        test_debug!("Walk from {:?} to {:?} (not in fork column {}), {} of {}", cur_block, block_ptr, fork_id, cnt, back_block);
        
        while cnt <= back_block {
            let next_block_ptr = match self.fork_ids.get(&block_ptr) {
                Some(ref fork_ptr) => {
                    let parent_fork_id = fork_ptr.parent_fork_id;
                    let parent_index = fork_ptr.parent_index;
                    let fork_column = &self.fork_table[parent_fork_id];

                    if fork_ptr.fork_id == fork_ptr.parent_fork_id && fork_ptr.index == fork_ptr.parent_index {
                        // at root
                        break;
                    }

                    test_debug!("cnt = {}, back_block = {}, parent_fork_id = {}, parent_index = {}", cnt, back_block, parent_fork_id, parent_index);

                    // in the parent's fork column?
                    if back_block - cnt <= parent_index {
                        let idx = parent_index - (back_block - cnt);
                        test_debug!("Found: parent_fork_id = {}, index = {} = {} - ({} - {}), target = {:?}", parent_fork_id, idx, parent_index, back_block, cnt, &fork_column[idx]);
                        return Ok(fork_column[idx].clone());
                    }
                    
                    // skip the rest of the fork column
                    cnt += parent_index;

                    test_debug!("Step from {:?} to {:?} ({} steps): {} of {}", block_ptr, &fork_column[0], parent_index, cnt, back_block);
                    fork_column[0].clone()
                },
                None => {
                    return Err(Error::CorruptionError(format!("No fork ID for {:?}", &block_ptr)));
                }
            };
            block_ptr = next_block_ptr;
            test_debug!("walk from {:?} to {:?}, {} of {}", block_ptr, next_block_ptr, cnt, back_block);
        }
        
        test_debug!("Not enough ancestors of {:?} (found only {})", cur_block, cnt);
        return Err(Error::NotFoundError);
    }

    pub fn contains(&self, bhh: &BlockHeaderHash) -> bool {
        self.fork_ids.contains_key(bhh)
    }

    pub fn get_parent(&self, bhh: &BlockHeaderHash) -> Result<BlockHeaderHash, Error> {
        self.walk_back(bhh, 1)
    }

    pub fn chain_tips(&self) -> Vec<BlockHeaderHash> {
        let mut ret = Vec::with_capacity(self.fork_ids.len());
        for fork_id in 0..self.fork_table.len() {
            ret.push(self.fork_table[fork_id][self.fork_table[fork_id].len() - 1].clone());
        }
        ret
    }

    pub fn clear(&mut self) -> () {
        self.fork_ids.clear();
        self.fork_table.clear();
    }

    pub fn size(&self) -> usize {
        self.fork_ids.len()
    }
}

// disk-backed Trie.
// Keeps the last-extended Trie in-RAM and flushes it to disk on either a call to flush() or a call
// to extend() with a different block header hash.
pub struct TrieFileStorage {
    dir_path: String,
    readonly: bool,

    last_extended: Option<BlockHeaderHash>,
    last_extended_trie: Option<TrieRAM>,
    
    cur_block: BlockHeaderHash,
    cur_block_fd: Option<fs::File>,
    
    read_count: u64,
    read_backptr_count: u64,
    read_node_count: u64,
    read_leaf_count: u64,

    write_count: u64,
    write_backptr_count: u64,
    write_node_count: u64,
    write_leaf_count: u64,

    // map chain tips to the list of their ancestors
    fork_table: TrieForkTable,

    // cache of block paths (they're surprisingly expensive to generate)
    block_path_cache: HashMap<BlockHeaderHash, String>
}

impl TrieFileStorage {
    pub fn new(dir_path: &String) -> Result<TrieFileStorage, Error> {
        match fs::metadata(dir_path) {
            Ok(md) => {
                if !md.is_dir() {
                    return Err(Error::NotDirectoryError);
                }
            },
            Err(e) => {
                if e.kind() != io::ErrorKind::NotFound {
                    return Err(Error::IOError(e));
                }
                // try to make it
                fs::create_dir_all(dir_path)
                    .map_err(Error::IOError)?;
            }
        }
        
        let fork_table = TrieFileStorage::read_fork_table(dir_path, &TrieFileStorage::block_sentinel())?;

        let ret = TrieFileStorage {
            dir_path: dir_path.clone(),
            readonly: false,

            last_extended: None,
            last_extended_trie: None,

            cur_block: TrieFileStorage::block_sentinel(),
            cur_block_fd: None,
            
            read_count: 0,
            read_backptr_count: 0,
            read_node_count: 0,
            read_leaf_count: 0,

            write_count: 0,
            write_backptr_count: 0,
            write_node_count: 0,
            write_leaf_count: 0,

            fork_table: fork_table,
            block_path_cache: HashMap::new()
        };

        Ok(ret)
    }

    pub fn block_sentinel() -> BlockHeaderHash {
        BlockHeaderHash([255u8; 32])
    }

    pub fn stats(&mut self) -> (u64, u64) {
        let r = self.read_count;
        let w = self.write_count;
        self.read_count = 0;
        self.write_count = 0;
        (r, w)
    }
    
    pub fn node_stats(&mut self) -> (u64, u64, u64, u64) {
        let nr = self.read_node_count;
        let br = self.read_backptr_count;
        let nw = self.write_node_count;
        let bw = self.write_backptr_count;

        self.read_node_count = 0;
        self.read_backptr_count = 0;
        self.write_node_count = 0;
        self.write_backptr_count = 0;

        (nr, br, nw, bw)
    }

    pub fn leaf_stats(&mut self) -> (u64, u64) {
        let lr = self.read_leaf_count;
        let lw = self.write_leaf_count;

        self.read_leaf_count = 0;
        self.write_leaf_count = 0;

        (lr, lw)
    }

    // last two bytes form the directory name
    fn block_dir(dir_path: &String, bhh: &BlockHeaderHash) -> PathBuf {
        let bhh_bytes = bhh.as_bytes();
        let bhh_1 = format!("{:02x}", bhh_bytes[31]);
        let bhh_2 = format!("{:02x}", bhh_bytes[30]);
        let p = Path::new(dir_path)
                    .join(bhh_1)
                    .join(bhh_2);
        p
    }

    fn block_path(dir_path: &String, bhh: &BlockHeaderHash) -> PathBuf {
        // it looks awkward, but it's waaaay faster than just doing to_hex()
        let bhh_bytes = bhh.as_bytes();
        let bhh_name = format!("{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}",
                              bhh_bytes[0],     bhh_bytes[1],       bhh_bytes[2],       bhh_bytes[3],
                              bhh_bytes[4],     bhh_bytes[5],       bhh_bytes[6],       bhh_bytes[7],
                              bhh_bytes[8],     bhh_bytes[9],       bhh_bytes[10],      bhh_bytes[11],
                              bhh_bytes[12],    bhh_bytes[13],      bhh_bytes[14],      bhh_bytes[15],
                              bhh_bytes[16],    bhh_bytes[17],      bhh_bytes[18],      bhh_bytes[19],
                              bhh_bytes[20],    bhh_bytes[21],      bhh_bytes[22],      bhh_bytes[23],
                              bhh_bytes[24],    bhh_bytes[25],      bhh_bytes[26],      bhh_bytes[27],
                              bhh_bytes[28],    bhh_bytes[29],      bhh_bytes[30],      bhh_bytes[31]);

        TrieFileStorage::block_dir(dir_path, bhh).join(bhh_name)
    }

    fn read_block_parent(dir_path: &String, bhh: &BlockHeaderHash) -> Result<BlockHeaderHash, Error> {
        let block_path = TrieFileStorage::block_path(dir_path, bhh);
        let mut fd = fs::OpenOptions::new()
                    .read(true)
                    .write(false)
                    .open(&block_path)
                    .map_err(|e| {
                        if e.kind() == io::ErrorKind::NotFound {
                            test_debug!("Not found: {:?}", &block_path);
                            Error::NotFoundError
                        }
                        else {
                            Error::IOError(e)
                        }
                    })?;

        let mut hashbuf = Vec::with_capacity(TRIEHASH_ENCODED_SIZE);
        fseek(&mut fd, 0)?;
        _read_hash_bytes(&mut fd, &mut hashbuf)?;

        let mut hashbuf_slice = [0u8; TRIEHASH_ENCODED_SIZE];
        hashbuf_slice.copy_from_slice(&hashbuf[0..TRIEHASH_ENCODED_SIZE]);

        Ok(BlockHeaderHash(hashbuf_slice))
    }

    /// Scan the block directory and get all child --> parent mappings
    /// and parent --> [children] mappings
    fn scan_blocks(dir_path: &String) -> Result<HashMap<BlockHeaderHash, Vec<BlockHeaderHash>>, Error> {
        let mut parent_children : HashMap<BlockHeaderHash, Vec<BlockHeaderHash>> = HashMap::new();

        for dir_1_res in fs::read_dir(dir_path).map_err(Error::IOError)? {
            let dir_1_entry = dir_1_res.map_err(Error::IOError)?;
            for dir_2_res in fs::read_dir(&dir_1_entry.path()).map_err(Error::IOError)? {
                let dir_2_entry = dir_2_res.map_err(Error::IOError)?;
                for block_file_res in fs::read_dir(&dir_2_entry.path()).map_err(Error::IOError)? {
                    let block_file = block_file_res.map_err(Error::IOError)?;
                    if !block_file.path().is_file() {
                        test_debug!("Skip {:?}", &block_file.path());
                        continue;
                    }

                    let block_path = block_file.path();
                    let block_name_opt = block_path.file_name();
                    let block_name = match block_name_opt {
                        Some(name) => match name.to_str() {
                            Some(name_str) => name_str.to_string(),
                            None => {
                                test_debug!("Skip {:?}", &block_path);
                                continue;
                            }
                        },
                        None => {
                            test_debug!("Skip {:?}", &block_path);
                            continue;
                        }
                    };

                    let bhh = match BlockHeaderHash::from_hex(&block_name) {
                        Ok(h) => h,
                        Err(_) => {
                            test_debug!("Skip {:?}", &block_path);
                            continue;
                        }
                    };

                    let bhh_parent = TrieFileStorage::read_block_parent(dir_path, &bhh)?;
                    if parent_children.contains_key(&bhh_parent) {
                        match parent_children.get_mut(&bhh_parent) {
                            Some(ref mut children) => {
                                children.push(bhh);
                            },
                            None => {
                                unreachable!();
                            }
                        }
                    }
                    else {
                        parent_children.insert(bhh_parent, vec![bhh]);
                    }
                }
            }
        }
        
        Ok(parent_children)
    }

    fn read_fork_table(dir_path: &String, root_hash: &BlockHeaderHash) -> Result<TrieForkTable, Error> {
        // maps a block hash to its list of unique ancestors.
        // has an entry for block hashes that are either chain tips, or parents of two or more forks.
        let parent_children = TrieFileStorage::scan_blocks(dir_path)?;
        TrieForkTable::new(root_hash, &parent_children)
    }
}

impl TrieStorage for TrieFileStorage {
    fn extend(&mut self, bhh: &BlockHeaderHash) -> Result<(), Error> {
        if self.fork_table.size() > 0 {
            if !self.fork_table.contains(&self.cur_block) {
                return Err(Error::CorruptionError(format!("Current block {:?} not in fork table", &self.cur_block)));
            }
        }
        if self.fork_table.contains(bhh) {
            test_debug!("Block {:?} is in the fork table already", bhh);
            return Err(Error::ExistsError);
        }
        
        self.readonly = false;
        self.flush()?;

        let size_hint = match self.last_extended_trie {
            Some(ref trie_storage) => trie_storage.size_hint() * 2,
            None => (1024 * 1024)
        };

        let trie_buf = TrieRAM::new(bhh, size_hint);

        // create an empty file for this block, so we can't extend to it again
        let block_dir = TrieFileStorage::block_dir(&self.dir_path, bhh);
        let block_path = TrieFileStorage::block_path(&self.dir_path, bhh);
        match fs::metadata(&block_path) {
            Ok(_) => {
                test_debug!("Block path exists: {:?}", &block_path);
                return Err(Error::ExistsError);
            },
            Err(e) => {
                if e.kind() != io::ErrorKind::NotFound {
                    return Err(Error::IOError(e));
                }
                fs::create_dir_all(block_dir)
                    .map_err(Error::IOError)?;

                test_debug!("Extend from {:?} to {:?} in {:?}", &self.cur_block, bhh, &block_path);

                // write the file out and add its parent
                let mut fd = fs::OpenOptions::new()
                            .read(true)
                            .write(true)
                            .create_new(true)
                            .open(&block_path)
                            .map_err(|e| {
                                if e.kind() == io::ErrorKind::NotFound {
                                    test_debug!("Not found: {:?}", &block_path);
                                    Error::NotFoundError
                                }
                                else {
                                    Error::IOError(e)
                                }
                            })?;

                write_all(&mut fd, self.cur_block.as_bytes())?;
            }
        }

        // extend the fork table
        self.fork_table.extend(&self.cur_block, bhh)?;
       
        // update internal structures
        self.cur_block = bhh.clone();
        self.cur_block_fd = None;

        self.last_extended = Some(bhh.clone());
        self.last_extended_trie = Some(trie_buf);
                
        test_debug!("Extended to {:?} in {:?}", &self.cur_block, &block_path);
        Ok(())
    }

    fn open(&mut self, bhh: &BlockHeaderHash, readwrite: bool) -> Result<(), Error> {
        if Some(*bhh) == self.last_extended {
            // nothing to do -- we're already ready.
            // just clear out.
            self.cur_block_fd = None;
            self.cur_block = bhh.clone();
            self.readonly = !readwrite;
            return Ok(());
        }

        // opening a different Trie than the one we're extending
        let block_path = TrieFileStorage::block_path(&self.dir_path, bhh);
        let fd = fs::OpenOptions::new()
                    .read(true)
                    .write(readwrite)
                    .open(&block_path)
                    .map_err(|e| {
                        if e.kind() == io::ErrorKind::NotFound {
                            test_debug!("Not found: {:?}", &block_path);
                            Error::NotFoundError
                        }
                        else {
                            Error::IOError(e)
                        }
                    })?;

        self.cur_block = bhh.clone();
        self.cur_block_fd = Some(fd);
        self.readonly = !readwrite;
        Ok(())
    }
    
    fn tell(&self) -> BlockHeaderHash {
        self.cur_block.clone()
    }
    
    fn block_walk(&self, back_block: u32) -> Result<BlockHeaderHash, Error> {
        test_debug!("block_walk from {:?} back {}", &self.cur_block, back_block);
        let cur_block = self.fork_table.walk_back(&self.cur_block, back_block)?; 
        test_debug!("block_walk from {:?} back {} is {:?}", &self.cur_block, back_block, &cur_block);
        Ok(cur_block)
    }
    
    fn root_ptr(&self) -> u64 {
        if Some(self.cur_block) == self.last_extended {
            0
        }
        else {
            // first 32 bytes are the block parent hash 
            32
        }
    }

    fn readwrite(&self) -> bool {
        !self.readonly
    }

    fn format(&mut self) -> Result<(), Error> {
        if self.readonly {
            test_debug!("Read-only!");
            return Err(Error::ReadOnlyError);
        }

        // blow away and recreate the Trie directory
        fs::remove_dir_all(self.dir_path.clone())
            .map_err(Error::IOError)?;

        fs::create_dir_all(self.dir_path.clone())
            .map_err(Error::IOError)?;

        match self.last_extended_trie {
            Some(ref mut trie_storage) => trie_storage.format()?,
            None => {}
        };

        self.cur_block = TrieFileStorage::block_sentinel();
        self.cur_block_fd = None;
        self.last_extended = None;
        self.last_extended_trie = None;
        self.fork_table.clear();
        
        Ok(())
    }

    fn read_node_hash_bytes(&mut self, ptr: &TriePtr, buf: &mut Vec<u8>) -> Result<(), Error> {
        if Some(self.cur_block) == self.last_extended {
            // special case 
            assert!(self.last_extended_trie.is_some());
            return match self.last_extended_trie {
                Some(ref mut trie_storage) => trie_storage.read_node_hash_bytes(ptr, buf),
                None => unreachable!()
            };
        }

        // some other block
        match self.cur_block_fd {
            Some(ref mut f) => read_node_hash_bytes(f, ptr, buf),
            None => {
                test_debug!("Not found (no file is open)");
                Err(Error::NotFoundError)
            }
        }
    }

    // NOTE: ptr will not be treated as a backptr
    fn read_node(&mut self, ptr: &TriePtr) -> Result<(TrieNodeType, TrieHash), Error> {
        test_debug!("read_node({:?}): {:?}", &self.cur_block, ptr);

        self.read_count += 1;
        if is_backptr(ptr.id()) {
            self.read_backptr_count += 1;
        }
        else if ptr.id() == TrieNodeID::Leaf {
            self.read_leaf_count += 1;
        }
        else {
            self.read_node_count += 1;
        }
        
        let clear_ptr = TriePtr::new(clear_backptr(ptr.id()), ptr.chr(), ptr.ptr());

        if Some(self.cur_block) == self.last_extended {
            // special case
            assert!(self.last_extended_trie.is_some());
            return match self.last_extended_trie {
                Some(ref mut trie_storage) => trie_storage.read_node(&clear_ptr),
                None => unreachable!()
            };
        }

        // some other block
        match self.cur_block_fd {
            Some(ref mut f) => read_nodetype(f, &clear_ptr),
            None => {
                test_debug!("Not found (no file is open)");
                Err(Error::NotFoundError)
            }
        }
    }
    
    fn write_node(&mut self, node: &TrieNodeType, hash: TrieHash) -> Result<(), Error> {
        if self.readonly {
            test_debug!("Read-only!");
            return Err(Error::ReadOnlyError);
        }

        let disk_ptr = ftell(self)?;
        test_debug!("write_node({:?}): at {}: {:?} {:?}", &self.cur_block, disk_ptr, &hash, node);
        
        self.write_count += 1;
        match node {
            TrieNodeType::Leaf(ref data) => {
                self.write_leaf_count += 1;
            },
            _ => {
                self.write_node_count += 1;
            }
        }

        if Some(self.cur_block) == self.last_extended {
            // special case
            assert!(self.last_extended_trie.is_some());
            return match self.last_extended_trie {
                Some(ref mut trie_storage) => trie_storage.write_node(node, hash),
                None => unreachable!()
            };
        }

        match self.cur_block_fd {
            Some(ref mut f) => {
                match node {
                    TrieNodeType::Leaf(ref data) => write_node_bytes(f, data, hash),
                    TrieNodeType::Node4(ref data) => write_node_bytes(f, data, hash),
                    TrieNodeType::Node16(ref data) => write_node_bytes(f, data, hash),
                    TrieNodeType::Node48(ref data) => write_node_bytes(f, data, hash),
                    TrieNodeType::Node256(ref data) => write_node_bytes(f, data, hash),
                }?;
                Ok(())
            },
            None => {
                test_debug!("Not found (no file is open)");
                Err(Error::NotFoundError)
            }
        }
    }
    
    fn flush(&mut self) -> Result<(), Error> {
        // save the currently-bufferred Trie to disk
        match (self.last_extended.take(), self.last_extended_trie.take()) {
            (Some(ref bhh), Some(ref mut trie_storage)) => {
                let block_path = TrieFileStorage::block_path(&self.dir_path, bhh);
                
                test_debug!("Flush {:?} to {:?}", bhh, &block_path);

                let parent_bhh = match self.fork_table.get_parent(bhh) {
                    Ok(parent) => {
                        parent
                    },
                    Err(e) => {
                        if self.fork_table.contains(bhh) {
                            // first block ever dumped
                            TrieFileStorage::block_sentinel()
                        }
                        else {
                            return Err(e);
                        }
                    }
                };

                let mut fd = fs::OpenOptions::new()
                            .read(false)
                            .write(true)
                            .truncate(true)
                            .open(&block_path)
                            .map_err(|e| {
                                if e.kind() == io::ErrorKind::NotFound {
                                    test_debug!("Not found: {:?}", &block_path);
                                    Error::NotFoundError
                                }
                                else {
                                    Error::IOError(e)
                                }
                            })?;

                test_debug!("Flush: parent of {:?} is {:?}", bhh, parent_bhh);
                trie_storage.dump(&mut fd, bhh, &parent_bhh)?;
            },
            (None, None) => {},
            (_, _) => {
                // should never happen 
                panic!("Inconsistent state: have either block header hash or trie IO buffer, but not both");
            }
        }

        if !self.readonly {
            match self.cur_block_fd {
                Some(ref mut f) => f.flush().map_err(Error::IOError)?,
                None => {}
            };
        }

        Ok(())
    }

    fn num_blocks(&self) -> usize {
        self.fork_table.size()
    }
}

impl Seek for TrieFileStorage {
    fn seek(&mut self, pos: SeekFrom) -> io::Result<u64> {
        if Some(self.cur_block) == self.last_extended {
            assert!(self.last_extended_trie.is_some());
            return match self.last_extended_trie {
                Some(ref mut trie_storage) => trie_storage.seek(pos),
                None => unreachable!()
            };
        }

        match self.cur_block_fd {
            Some(ref mut f) => f.seek(pos),
            None => Err(io::Error::new(io::ErrorKind::Other, Error::BadSeekValue))
        }
    }
}

pub struct Trie<S: TrieStorage + Seek> {
    _phantom: PhantomData<S>
}

impl<S> Trie<S>
where
    S: TrieStorage + Seek
{
    fn format(s: &mut S, bhh: &BlockHeaderHash) -> Result<(), Error> {
        s.format()?;
        s.extend(bhh)?;
        let node = TrieNode256::new(&vec![]);
        let hash = get_node_hash(&node, &vec![]);
        s.write_node(&TrieNodeType::Node256(node), hash)
    }

    fn read_root(s: &mut S) -> Result<(TrieNodeType, TrieHash), Error> {
        let ptr = TriePtr::new(set_backptr(TrieNodeID::Node256), 0, s.root_ptr() as u32);
        let res = s.read_node(&ptr);
        match res {
            Err(Error::CorruptionError(_)) => {
                let non_backptr_ptr = TriePtr::new(TrieNodeID::Node256, 0, s.root_ptr() as u32);
                s.read_node(&non_backptr_ptr)
            },
            Err(e) => Err(e),
            Ok(data) => Ok(data)
        }

    }

    fn read_node(s: &mut S, ptr: &TriePtr) -> Result<(TrieNodeType, TrieHash), Error> {
        s.read_node(ptr)
    }

    fn write_nodetype(s: &mut S, node: &TrieNodeType, hash: TrieHash) -> Result<(), Error> {
        s.write_node(node, hash)
    }
    
    fn write_node<T: TrieNode + std::fmt::Debug>(s: &mut S, node: &T, hash: TrieHash) -> Result<(), Error> {
        match node.id() {
            TrieNodeID::Node4 => s.write_node(&node.try_as_node4().unwrap(), hash),
            TrieNodeID::Node16 => s.write_node(&node.try_as_node16().unwrap(), hash),
            TrieNodeID::Node48 => s.write_node(&node.try_as_node48().unwrap(), hash),
            TrieNodeID::Node256 => s.write_node(&node.try_as_node256().unwrap(), hash),
            TrieNodeID::Leaf => s.write_node(&node.try_as_leaf().unwrap(), hash),
            _ => panic!("Unknown node type {}", node.id())
        }
    }
     
    /// Walk from the given node to the next node on the path, advancing the cursor.
    /// Return the TriePtr followed, the _next_ node to walk, and the hash of the _current_ node.
    /// Returns None if we either didn't find the node, or we're out of path, or we're at a leaf.
    /// NOTE: This only works if we're walking a Trie, not a MARF.  Returns Ok(None) if a BackPtr
    /// is found.
    fn walk_from(s: &mut S, node: &TrieNodeType, c: &mut TrieCursor) -> Result<Option<(TriePtr, TrieNodeType, TrieHash)>, Error> {
        let ptr_opt = c.walk(node, &s.tell());
        match ptr_opt {
            None => {
                // not found, or found a BackPtr
                Ok(None)
            },
            Some(ptr) => {
                test_debug!("Walked to {:?}", &ptr);
                let (node, hash) = Trie::read_node(s, &ptr)?;
                Ok(Some((ptr, node, hash)))
            }
        }
    }

    // s.tell() will refer to the block from which the node was read
    fn walk_backptr(s: &mut S, ptr: &TriePtr, c: &mut TrieCursor) -> Result<(TrieNodeType, TrieHash, TriePtr), Error> {
        if !is_backptr(ptr.id()) {
            // child is in this block
            if ptr.id() == TrieNodeID::Empty {
                // shouldn't happen
                return Err(Error::CorruptionError("ptr is empty".to_string()));
            }
            let (node, node_hash) = s.read_node(ptr)?;
            return Ok((node, node_hash, ptr.clone()));
        }
        else {
            // ptr is a backptr
            let back_block_hash = s.block_walk(ptr.back_block())?;
            s.open(&back_block_hash, false)?;

            let backptr = ptr.from_backptr();
            let (node, node_hash) = s.read_node(&backptr)?;

            c.walk_backptr_step_backptr(&node, &backptr, &s.tell());
            Ok((node, node_hash, backptr))
        }
    }
 
    /// Read a sequence of hashes given a node's ptrs.
    /// If a ptr is a backptr, go and resolve the hash by walking back.
    /// On err, S may point to a prior block.  The caller should call s.open(...) if an error
    /// occurs.
    fn read_child_hashes_bytes(s: &mut S, ptrs: &[TriePtr], buf: &mut Vec<u8>) -> Result<(), Error> {
        // "for ptr in ptrs.iter()" is actually kinda slow, so do this instead
        let mut i = 0;
        while i < ptrs.len() {
            let ptr = &ptrs[i];
            if ptr.id() == TrieNodeID::Empty {
                // hash of empty string
                // buf.extend_from_slice(TrieHash::from_data(&[]).as_bytes());
                fast_extend_from_slice(buf, TrieHash::from_data(&[]).as_bytes());
            }
            else if !is_backptr(ptr.id()) {
                // hash is in the same block as this node
                s.read_node_hash_bytes(ptr, buf)?;
            }
            else {
                fast_extend_from_slice(buf, TrieHash::from_data(&[]).as_bytes());
                /*
                // hash the full pointer to this node, and pass *that* in
                let back_block_hash = s.block_walk(ptr.back_block())?;
                let mut ptr_buf = Vec::with_capacity((BLOCK_HEADER_HASH_ENCODED_SIZE as usize) + (TRIEPTR_SIZE as usize));
                fast_extend_from_slice(&mut ptr_buf, back_block_hash.as_bytes());
                ptr.to_bytes(&mut ptr_buf);

                let h = TrieHash::from_data(&ptr_buf[..]);
                fast_extend_from_slice(buf, h.as_bytes());
                */
                /*
                // hash is in a prior block
                let back_block_hash = s.block_walk(ptr.back_block())?;
                let backptr = ptr.from_backptr();

                // save storage state
                let cur_block_hash = s.tell();
                let cur_block_rw = s.readwrite();
                s.open(&back_block_hash, false)?;

                s.read_node_hash_bytes(&backptr, buf)?;

                // restore state
                s.open(&cur_block_hash, cur_block_rw)?;
                */
            }
            i += 1;
        }
        assert_eq!(buf.len() % TRIEHASH_ENCODED_SIZE, 0);
        Ok(())
    }

    /// Read a node's children's hashes as a contiguous byte vector.
    /// This only works for intermediate nodes and leafs (the latter of which have no children).
    /// A BackPtr cannot be handled since the node it refers to is in another Trie.
    /// On Err, s may point to a different block hash
    fn get_children_hashes_bytes(s: &mut S, node: &TrieNodeType, buf: &mut Vec<u8>) -> Result<(), Error> {
        test_debug!("get_children_hashes_bytes for {:?}", node);
        let cur_block_hash = s.tell();
        match node {
            TrieNodeType::Leaf(_) => {
                Ok(())
            },
            TrieNodeType::Node4(ref data) => {
                Trie::read_child_hashes_bytes(s, &data.ptrs, buf)?;
                Ok(())
            },
            TrieNodeType::Node16(ref data) => {
                Trie::read_child_hashes_bytes(s, &data.ptrs, buf)?;
                Ok(())
            },
            TrieNodeType::Node48(ref data) => {
                Trie::read_child_hashes_bytes(s, &data.ptrs, buf)?;
                Ok(())
            },
            TrieNodeType::Node256(ref data) => {
                Trie::read_child_hashes_bytes(s, &data.ptrs, buf)?;
                Ok(())
            }
        }
    }

    /// Read a node's children's hashes.
    /// On Err, s may point to a different block hash
    fn get_children_hashes(s: &mut S, node: &TrieNodeType) -> Result<Vec<TrieHash>, Error> {
        let max_hashes = match node {
            TrieNodeType::Leaf(_) => 0,
            TrieNodeType::Node4(_) => 4,
            TrieNodeType::Node16(_) => 16,
            TrieNodeType::Node48(_) => 48,
            TrieNodeType::Node256(_) => 256
        };

        let mut hashes_buf = Vec::with_capacity(TRIEHASH_ENCODED_SIZE * max_hashes);
        Trie::get_children_hashes_bytes(s, &node, &mut hashes_buf)?;

        // extract individual hashes
        let mut all_hashes = Vec::with_capacity(hashes_buf.len() / TRIEHASH_ENCODED_SIZE);
        for i in 0..hashes_buf.len() / TRIEHASH_ENCODED_SIZE {
            let mut h_slice = [0u8; TRIEHASH_ENCODED_SIZE];
            h_slice.copy_from_slice(&hashes_buf[TRIEHASH_ENCODED_SIZE*i..TRIEHASH_ENCODED_SIZE*(i+1)]);
            all_hashes.push(TrieHash(h_slice))
        }
        Ok(all_hashes)
    }

    /// Given a leaf, replace it.
    /// c must point to the value to replace
    fn replace_leaf(s: &mut S, c: &TrieCursor, value: &mut TrieLeaf) -> Result<TriePtr, Error> {
        fseek(s, c.ptr().ptr() as u64)?;
        
        let (cur_leaf, _) = Trie::read_node(s, &c.ptr())?;
        match cur_leaf {
            TrieNodeType::Leaf(ref data) => {
                value.path = data.path.clone();
            },
            _ => {
                return Err(Error::CorruptionError(format!("Not a leaf: {:?}", &c.ptr())));
            }
        }

        let leaf_hash = get_node_hash(value, &vec![]);
        fseek(s, c.ptr().ptr() as u64)?;
        Trie::write_node(s, value, leaf_hash.clone())?;

        test_debug!("replace_leaf: wrote {:?} at {:?}", value, &c.ptr());
        Ok(c.ptr())
    }

    /// Append a leaf to the trie, and return the TriePtr to it.
    /// Do lazy expansion -- have the leaf store the trailing path to it.
    /// Return the TriePtr to the newly-written leaf
    fn append_leaf(s: &mut S, c: &TrieCursor, value: &mut TrieLeaf) -> Result<TriePtr, Error> {
        assert!(c.chr().is_some());

        let ptr = fseek_end(s)?;
        let chr = c.chr().unwrap();
        let leaf_path = &c.path.as_bytes()[c.index..];

        value.path = leaf_path.to_vec();
        let leaf_hash = get_node_hash(value, &vec![]);

        Trie::write_node(s, value, leaf_hash)?;
       
        let leaf_ptr = TriePtr::new(TrieNodeID::Leaf, chr, ptr as u32);
        test_debug!("append_leaf: append {:?} at {:?}", value, &leaf_ptr);
        Ok(leaf_ptr)
    }

    /// Given a leaf and a cursor that is _not_ EOP, and a new leaf, create a node4 with the two
    /// leaves as its children and return its pointer.
    ///
    /// f must point to the start of cur_leaf.
    ///
    /// aabbccddeeff00112233=123456
    ///
    /// insert (aabbccddeeff99887766, 98765)
    ///
    ///              [00]112233=123456
    ///             /
    /// aabbccddeeff
    ///             \
    ///              [99]887766=98765
    ///
    fn promote_leaf_to_node4(s: &mut S, c: &mut TrieCursor, cur_leaf_data: &mut TrieLeaf, new_leaf_data: &mut TrieLeaf) -> Result<TriePtr, Error> {
        // can only work if we're not at the end of the path, and the current node has a path
        assert!(!c.eop());
        assert!(cur_leaf_data.path.len() > 0);

        // switch from lazy expansion to path compression --
        // * the current and new leaves will have unique suffixes
        // * the node4 will have their shared prefix
        let cur_leaf_ptr = c.ptr();
        let node4_path = cur_leaf_data.path[0..(if c.ntell() == 0 { 0 } else { c.ntell() })].to_vec();
        let node4_chr = cur_leaf_ptr.chr();

        let cur_leaf_chr = cur_leaf_data.path[c.ntell()];
        let cur_leaf_path = cur_leaf_data.path[(if c.ntell() >= cur_leaf_data.path.len() { c.ntell() } else { c.ntell() + 1 })..].to_vec();

        // update current leaf (path changed) and save it
        let cur_leaf_disk_ptr = ftell(s)?;
        let cur_leaf_new_ptr = TriePtr::new(TrieNodeID::Leaf, cur_leaf_chr, cur_leaf_disk_ptr as u32);

        assert!(cur_leaf_path.len() <= cur_leaf_data.path.len());
        let sav_cur_leaf_data = cur_leaf_data.clone();
        cur_leaf_data.path = cur_leaf_path;
        let cur_leaf_hash = get_node_hash(cur_leaf_data, &vec![]);

        // NOTE: this is safe since the current leaf's byte representation has gotten shorter
        Trie::write_node(s, cur_leaf_data, cur_leaf_hash.clone())?;
        
        // append the new leaf and the end of the file.
        let new_leaf_disk_ptr = fseek_end(s)?;
        let new_leaf_chr = c.path[c.tell()];        // NOTE: this is safe because !c.eop()
        let new_leaf_path = c.path[(if c.tell()+1 <= c.path.len() { c.tell()+1 } else { c.path.len() })..].to_vec();
        new_leaf_data.path = new_leaf_path;
        let new_leaf_hash = get_node_hash(new_leaf_data, &vec![]);

        Trie::write_node(s, new_leaf_data, new_leaf_hash.clone())?;

        let new_leaf_ptr = TriePtr::new(TrieNodeID::Leaf, new_leaf_chr, new_leaf_disk_ptr as u32);

        // append the Node4 that points to both of them, and put it after the new leaf
        let node4_disk_ptr = fseek_end(s)?;
        let mut node4_data = TrieNode4::new(&node4_path);

        assert!(node4_data.insert(&cur_leaf_new_ptr));
        assert!(node4_data.insert(&new_leaf_ptr));

        let node4_hash = get_node_hash(&node4_data, &vec![cur_leaf_hash, new_leaf_hash, TrieHash::from_data(&[]), TrieHash::from_data(&[])]);

        Trie::write_node(s, &node4_data, node4_hash.clone())?;

        let ret = TriePtr::new(TrieNodeID::Node4, node4_chr, node4_disk_ptr as u32);
        c.retarget(&TrieNodeType::Node4(node4_data.clone()), &ret, &s.tell());

        test_debug!("Promoted {:?} to {:?}, {:?}, {:?}, new ptr = {:?}", sav_cur_leaf_data, cur_leaf_data, &node4_data, new_leaf_data, &ret);
        Ok(ret)
    }

    fn node_has_space(chr: u8, children: &[TriePtr]) -> bool {
        let mut i = (children.len() - 1) as i64;
        while i >= 0 {
            if children[i as usize].id() == TrieNodeID::Empty || children[i as usize].chr() == chr {
                return true;
            }
            i -= 1;
        }
        return false;
    }

    /// Try to insert a leaf node into the given node, if there's space to do so and if the leaf
    /// belongs as a child of this node.
    /// If so, then save the leaf and its hash, update the node's ptrs and hash, and return the
    /// node's ptr and the node's new hash so we can update the trie.
    /// Return None if there's no space, or if the leaf doesn't share its full path prefix with the
    /// given node.
    ///
    ///              [00]112233 ...
    ///             /
    /// aabbccddeeff 
    ///
    /// insert (aabbccddeeff99887766, 123456)
    ///
    ///              [00]112233 ...
    ///             /
    /// aabbccddeeff
    ///             \
    ///              [99]887766=123456
    ///
    fn try_attach_leaf(s: &mut S, c: &TrieCursor, leaf: &mut TrieLeaf, node: &mut TrieNodeType) -> Result<Option<TriePtr>, Error> {
        // can only do this if we're at the end of the node's path
        if !c.eonp(node) {
            // nope
            return Ok(None);
        }
        assert!(c.chr().is_some());

        fn attach_leaf<T: TrieNode + fmt::Debug, S: TrieStorage + Seek>(s: &mut S, c: &TrieCursor, leaf: &mut TrieLeaf, node_data: &mut T) -> Result<Option<TriePtr>, Error> {
            let has_space = Trie::<S>::node_has_space(c.chr().unwrap(), node_data.ptrs());
            if !has_space {
                // nope!
                return Ok(None);
            }
            // write leaf and update parent
            let leaf_ptr = Trie::append_leaf(s, c, leaf)?;
            let inserted = node_data.insert(&leaf_ptr);

            assert!(inserted);

            let mut node_hashes_bytes = Vec::with_capacity(node_data.ptrs().len() * TRIEHASH_ENCODED_SIZE);
            Trie::read_child_hashes_bytes(s, node_data.ptrs(), &mut node_hashes_bytes)?;
            let new_node_hash = get_node_hash_bytes(node_data, &node_hashes_bytes);

            fseek(s, c.ptr().ptr() as u64)?;
            Trie::write_node(s, node_data, new_node_hash)?;
            
            Ok(Some(c.ptr()))
        }

        match node {
            TrieNodeType::Leaf(_) => panic!("Cannot insert into leaf"),
            TrieNodeType::Node4(ref mut data) => attach_leaf(s, c, leaf, data),
            TrieNodeType::Node16(ref mut data) => attach_leaf(s, c, leaf, data),
            TrieNodeType::Node48(ref mut data) => attach_leaf(s, c, leaf, data),
            TrieNodeType::Node256(ref mut data) => attach_leaf(s, c, leaf, data)
        }
    }

    /// Given a node and a leaf, attach the leaf.  Promote the intermediate node if necessary.
    /// Does the same thing as try_attach_leaf, but the node might get expanaded.  In this case, the
    /// new node will be appended and the old node will be leaked.
    fn insert_leaf(s: &mut S, c: &mut TrieCursor, leaf: &mut TrieLeaf, node: &mut TrieNodeType) -> Result<TriePtr, Error> {
        // can only do this if we're at the end of the node's path
        assert!(c.eonp(node));

        let res = Trie::try_attach_leaf(s, c, leaf, node)?;
        if res.is_some() {
            // success!
            return Ok(res.unwrap());
        }

        fn inner_insert_leaf<T: TrieNode + fmt::Debug, S: TrieStorage + Seek>(s: &mut S, c: &TrieCursor, leaf: &mut TrieLeaf, new_node_data: &mut T) -> Result<TriePtr, Error> {
            let node_ptr = c.ptr();
            let leaf_ptr = Trie::append_leaf(s, c, leaf)?;
            let inserted = new_node_data.insert(&leaf_ptr);
            assert!(inserted);
        
            let mut node_hashes_bytes = Vec::with_capacity(new_node_data.ptrs().len() * TRIEHASH_ENCODED_SIZE);
            Trie::read_child_hashes_bytes(s, new_node_data.ptrs(), &mut node_hashes_bytes)?;
            let new_node_hash = get_node_hash_bytes(new_node_data, &node_hashes_bytes);

            let new_node_disk_ptr = fseek_end(s)?;
            Trie::write_node(s, new_node_data, new_node_hash)?;
            
            // give back the promoted node's ptr
            Ok(TriePtr::new(new_node_data.id(), node_ptr.chr(), new_node_disk_ptr as u32))
        }

        // need to promote node 
        match node {
            TrieNodeType::Leaf(_) => panic!("Cannot insert into a leaf"),
            TrieNodeType::Node4(ref data) => {
                let mut new_node = TrieNode16::from_node4(data);
                let ret = inner_insert_leaf(s, c, leaf, &mut new_node)?;
                c.retarget(&TrieNodeType::Node16(new_node), &ret, &s.tell());
                Ok(ret)
            },
            TrieNodeType::Node16(ref data) => {
                let mut new_node = TrieNode48::from_node16(data);
                let ret = inner_insert_leaf(s, c, leaf, &mut new_node)?;
                c.retarget(&TrieNodeType::Node48(new_node), &ret, &s.tell());
                Ok(ret)
            },
            TrieNodeType::Node48(ref data) => {
                let mut new_node = TrieNode256::from_node48(data);
                let ret = inner_insert_leaf(s, c, leaf, &mut new_node)?;
                c.retarget(&TrieNodeType::Node256(new_node), &ret, &s.tell());
                Ok(ret)
            },
            TrieNodeType::Node256(_) => panic!("Somehow could not insert into a Node256")
        }
    }

    /// Given a node and a leaf to insert, break apart the node's compressed path into the shared
    /// prefix and the node- and leaf-specific segments, and add a Node4 at the break with the
    /// leaf.  Updates the given node and leaf, and returns the node4's ptr and hash.
    ///
    ///                            [00]112233 ...
    ///                           /
    /// (parent) -- [aa]bbccddeeff 
    ///              (node-X)     \
    ///                            [99]887766 ...
    ///
    /// insert (aabbccffccbbaa, 123456)
    ///
    ///                      [ff]ccbbaa=123456
    ///                     /
    /// (parent) -- [aa]bbcc -- [dd]eeff -- [00]112233 ...
    ///             (node-X')  (node-X) \
    ///                                  [99]887766 ...
    ///
    fn splice_leaf(s: &mut S, c: &mut TrieCursor, leaf: &mut TrieLeaf, node: &mut TrieNodeType) -> Result<TriePtr, Error> {
        assert!(!c.eop());
        assert!(!c.eonp(node));
        assert!(c.chr().is_some());

        let node_path = match node {
            TrieNodeType::Leaf(_) => panic!("Intermediate node should not be a leaf"),
            TrieNodeType::Node4(ref data) => data.path.clone(),
            TrieNodeType::Node16(ref data) => data.path.clone(),
            TrieNodeType::Node48(ref data) => data.path.clone(),
            TrieNodeType::Node256(ref data) => data.path.clone()
        };

        let shared_path_prefix = node_path[0..c.ntell()].to_vec();
        let leaf_path = c.path[c.tell()+1..].to_vec();
        let new_cur_node_path = node_path[c.ntell()+1..].to_vec();
        let new_cur_node_chr = node_path[c.ntell()];        // chr for node-X post-update

        // store leaf 
        leaf.path = leaf_path;
        let leaf_chr = c.path[c.tell()];
        let leaf_disk_ptr = fseek_end(s)?;
        let leaf_hash = get_node_hash(leaf, &vec![]);
        let leaf_ptr = TriePtr::new(TrieNodeID::Leaf, leaf_chr, leaf_disk_ptr as u32);
        Trie::write_node(s, leaf, leaf_hash.clone())?;
       
        // update current node (node-X) and make a new path and ptr for it
        let cur_node_cur_ptr = c.ptr();
        let new_cur_node_disk_ptr = fseek_end(s)?;
        let new_cur_node_ptr = TriePtr::new(cur_node_cur_ptr.id(), new_cur_node_chr, new_cur_node_disk_ptr as u32);

        fseek(s, cur_node_cur_ptr.ptr() as u64)?;
        let mut node_hashes_bytes = Vec::with_capacity(TRIEHASH_ENCODED_SIZE * 256);
        Trie::get_children_hashes_bytes(s, &node, &mut node_hashes_bytes)?;

        let new_cur_node_hash = match node {
            TrieNodeType::Leaf(_) => panic!("Intermediate node should not be a leaf"),
            TrieNodeType::Node4(ref mut data) => {
                data.path = new_cur_node_path;
                get_node_hash_bytes(data, &node_hashes_bytes)
            },
            TrieNodeType::Node16(ref mut data) => {
                data.path = new_cur_node_path;
                get_node_hash_bytes(data, &node_hashes_bytes)
            },
            TrieNodeType::Node48(ref mut data) => {
                data.path = new_cur_node_path;
                get_node_hash_bytes(data, &node_hashes_bytes)
            },
            TrieNodeType::Node256(ref mut data) => {
                data.path = new_cur_node_path;
                get_node_hash_bytes(data, &node_hashes_bytes)
            }
        };

        // build node-X' -- same type of node, but will occupy less space than node-X since its
        // path is shorter
        let (new_node_id, new_node, new_node_hash) = match node {
            TrieNodeType::Leaf(_) => panic!("Tried to use a leaf as an intermediate node"),
            TrieNodeType::Node4(_) => {
                let mut new_node = TrieNode4::new(&shared_path_prefix);
                new_node.insert(&leaf_ptr);
                new_node.insert(&new_cur_node_ptr);
                let new_node_hash = get_node_hash(&new_node, &vec![leaf_hash, new_cur_node_hash, TrieHash::from_data(&[]), TrieHash::from_data(&[])]);
                (TrieNodeID::Node4, TrieNodeType::Node4(new_node), new_node_hash)
            },
            TrieNodeType::Node16(_) => {
                let mut new_node = TrieNode16::new(&shared_path_prefix);
                new_node.insert(&leaf_ptr);
                new_node.insert(&new_cur_node_ptr);
                let mut node_hashes = vec![leaf_hash, new_cur_node_hash];
                for i in 2..16 {
                    node_hashes.push(TrieHash::from_data(&[]));
                }
                let new_node_hash = get_node_hash(&new_node, &node_hashes);
                (TrieNodeID::Node16, TrieNodeType::Node16(new_node), new_node_hash)
            },
            TrieNodeType::Node48(_) => {
                let mut new_node = TrieNode48::new(&shared_path_prefix);
                new_node.insert(&leaf_ptr);
                new_node.insert(&new_cur_node_ptr);
                let mut node_hashes = vec![leaf_hash, new_cur_node_hash];
                for i in 2..48 {
                    node_hashes.push(TrieHash::from_data(&[]));
                }
                let new_node_hash = get_node_hash(&new_node, &node_hashes);
                (TrieNodeID::Node48, TrieNodeType::Node48(new_node), new_node_hash)
            },
            TrieNodeType::Node256(_) => {
                let mut new_node = TrieNode256::new(&shared_path_prefix);
                new_node.insert(&leaf_ptr);
                new_node.insert(&new_cur_node_ptr);
                let mut node_hashes = vec![];
                for i in 0..256 {
                    if (i as u8) == leaf_ptr.chr() {
                        node_hashes.push(leaf_hash.clone());
                    }
                    else if (i as u8) == new_cur_node_ptr.chr() {
                        node_hashes.push(new_cur_node_hash.clone());
                    }
                    else {
                        node_hashes.push(TrieHash::from_data(&[]));
                    }
                }
                let new_node_hash = get_node_hash(&new_node, &node_hashes);
                (TrieNodeID::Node256, TrieNodeType::Node256(new_node), new_node_hash)
            }
        };

        // store node-X' where node-X used to be
        fseek(s, cur_node_cur_ptr.ptr() as u64)?;
        Trie::write_nodetype(s, &new_node, new_node_hash.clone())?;

        // store node-X at the end
        fseek(s, new_cur_node_disk_ptr as u64)?;
        Trie::write_nodetype(s, node, new_cur_node_hash.clone())?;

        let ret = TriePtr::new(new_node_id, cur_node_cur_ptr.chr(), cur_node_cur_ptr.ptr());
        c.retarget(&new_node.clone(), &ret, &s.tell());

        test_debug!("splice_leaf: node-X' at {:?}", &ret);
        Ok(ret)
    }

    /// Add a new value to the Trie at the location pointed at by the cursor.
    /// Returns a ptr to be inserted into the last node visited by the cursor.
    fn add_value(s: &mut S, c: &mut TrieCursor, value: &mut TrieLeaf) -> Result<TriePtr, Error> {
        let mut node = match c.node() {
            Some(n) => n,
            None => panic!("Cursor is uninitialized")
        };

        if c.eop() {
            match node {
                TrieNodeType::Leaf(_) => {
                    return Trie::replace_leaf(s, c, value);
                },
                _ => {}
            };

            Trie::insert_leaf(s, c, value, &mut node)
        }
        else {
            // didn't reach the end of the path, so we're on an intermediate node
            // or we're somewhere in the path of a leaf.
            // Either tack the leaf on (possibly promoting the node), or splice the leaf in.
            if c.eonp(&node) {
                test_debug!("eop = {}, eonp = {}, c = {:?}, node = {:?}", c.eop(), c.eonp(&node), c, &node);
                Trie::insert_leaf(s, c, value, &mut node)
            }
            else {
                match node {
                    TrieNodeType::Leaf(ref mut data) => {
                        Trie::promote_leaf_to_node4(s, c, data, value)
                    },
                    _ => {
                        Trie::splice_leaf(s, c, value, &mut node)
                    }
                }
            }
        }
    }

    /// Unwind a TrieCursor to update the Merkle root of the trie.
    fn update_root_hash(s: &mut S, c: &TrieCursor) -> Result<(), Error> {
        assert!(c.node_ptrs.len() > 0);

        let mut ptrs = c.node_ptrs.clone();
        test_debug!("update_root_hash: ptrs = {:?}", &ptrs);
        let mut child_ptr = ptrs.pop().unwrap();

        while ptrs.len() > 0 {
            let ptr = match ptrs.pop() {
                Some(p) => p,
                None => panic!("Out of ptrs")
            };
            if is_backptr(ptr.id()) {
                // this node was not altered, but instead queued to the cursor as part of walking a
                // backptr skiplist.  Do nothing.
                continue;
            }

            let (mut node, cur_hash) = Trie::read_node(s, &ptr)?;

            // this child_ptr _must_ be in the node.
            let updated = match node {
                TrieNodeType::Leaf(_) => panic!("Leaf as intermediate (read {:?})", &ptr),
                TrieNodeType::Node4(ref mut data) => data.replace(&child_ptr),
                TrieNodeType::Node16(ref mut data) => data.replace(&child_ptr),
                TrieNodeType::Node48(ref mut data) => data.replace(&child_ptr),
                TrieNodeType::Node256(ref mut data) => data.replace(&child_ptr)
            };
            if !updated {
                test_debug!("FAILED TO UPDATE {:?} WITH {:?}: {:?}", &node, &child_ptr, c);
                assert!(updated);
            }

            let mut hash_buf = Vec::with_capacity(TRIEHASH_ENCODED_SIZE * 256);
            Trie::get_children_hashes_bytes(s, &node, &mut hash_buf)?;

            fseek(s, ptr.ptr() as u64)?;

            match node {
                TrieNodeType::Leaf(ref data) => {
                    let h = get_node_hash_bytes(data, &hash_buf);
                    test_debug!("update_root_hash: Updated {:?} with {:?} from {:?} to {:?}", data, &child_ptr, &cur_hash, &h);
                    Trie::write_node(s, data, h)?;
                },
                TrieNodeType::Node4(ref data) => {
                    let h = get_node_hash_bytes(data, &hash_buf);
                    test_debug!("update_root_hash: Updated {:?} with {:?} from {:?} to {:?}", data, &child_ptr, &cur_hash, &h);
                    Trie::write_node(s, data, h)?;
                },
                TrieNodeType::Node16(ref data) => {
                    let h = get_node_hash_bytes(data, &hash_buf);
                    test_debug!("update_root_hash: Updated {:?} with {:?} from {:?} to {:?}", data, &child_ptr, &cur_hash, &h);
                    Trie::write_node(s, data, h)?;
                },
                TrieNodeType::Node48(ref data) => {
                    let h = get_node_hash_bytes(data, &hash_buf);
                    test_debug!("update_root_hash: Updated {:?} with {:?} from {:?} to {:?}", data, &child_ptr, &cur_hash, &h);
                    Trie::write_node(s, data, h)?;
                },
                TrieNodeType::Node256(ref data) => {
                    let h = get_node_hash_bytes(data, &hash_buf);
                    test_debug!("update_root_hash: Updated {:?} with {:?} from {:?} to {:?}", data, &child_ptr, &cur_hash, &h);
                    Trie::write_node(s, data, h)?;
                }
            };
            
            child_ptr = ptr;
            child_ptr.id = clear_backptr(child_ptr.id);
        }

        // must be at the root
        assert_eq!(child_ptr, TriePtr::new(TrieNodeID::Node256,0,0));
        Ok(())
    }
}

/// Merklized Adaptive-Radix Forest -- a collection of Merklized Adaptive-Radix Tries
pub struct MARF<S>
where
    S: TrieStorage + Seek
{
    _phantom: PhantomData<S>
}

impl<S> MARF<S>
where
    S: TrieStorage + Seek
{

    // helper method for walking a node's backpr
    fn walk_backptr(s: &mut S, start_node: &TrieNodeType, chr: u8, c: &mut TrieCursor) -> Result<(TrieNodeType, TrieHash, TriePtr, u32), Error> {
        let ptr_opt = match start_node {
            TrieNodeType::Node4(ref data) => data.walk(chr),
            TrieNodeType::Node16(ref data) => data.walk(chr),
            TrieNodeType::Node48(ref data) => data.walk(chr),
            TrieNodeType::Node256(ref data) => data.walk(chr),
            _ => {
                panic!("Did not get an intermediate node");
            }
        };
        match ptr_opt {
            None => {
                // this node never had a child for this chr
                test_debug!("Failed to walk to '{}' from {:?}", chr, start_node);
                Err(Error::BackptrNotFoundError)
            },
            Some(ptr) => {
                test_debug!("Walk backptrs for {:?} to {:?} from {:?}", c, &ptr, &start_node);
                
                // this node had a child for this chr at one point
                let (node, node_hash, node_ptr) = match start_node {
                    TrieNodeType::Node4(ref data) => Trie::walk_backptr(s, &ptr, c)?,
                    TrieNodeType::Node16(ref data) => Trie::walk_backptr(s, &ptr, c)?,
                    TrieNodeType::Node48(ref data) => Trie::walk_backptr(s, &ptr, c)?,
                    TrieNodeType::Node256(ref data) => Trie::walk_backptr(s, &ptr, c)?,
                    _ => {
                        unreachable!();
                    }
                };

                Ok((node, node_hash, node_ptr, ptr.back_block))
            }
        }
    }
   
    fn node_copy_update(s: &mut S, node: &mut TrieNodeType, node_dist: u32) -> Result<TrieHash, Error> {
        fn node_copy_update_ptrs(ptrs: &mut [TriePtr], node_dist: u32) -> () {
            for i in 0..ptrs.len() {
                if ptrs[i].id() == TrieNodeID::Empty {
                    continue;
                }
                else if is_backptr(ptrs[i].id()) {
                    // increase depth
                    ptrs[i].back_block += node_dist;
                }
                else {
                    // make backptr
                    ptrs[i].back_block = node_dist;
                    ptrs[i].id = set_backptr(ptrs[i].id());
                }
            }
        }

        let hash = match node {
            TrieNodeType::Node4(ref mut data) => {
                node_copy_update_ptrs(&mut data.ptrs, node_dist);
                TrieHash::from_data(&[])
            },
            TrieNodeType::Node16(ref mut data) => {
                node_copy_update_ptrs(&mut data.ptrs, node_dist);
                TrieHash::from_data(&[])
            },
            TrieNodeType::Node48(ref mut data) => {
                node_copy_update_ptrs(&mut data.ptrs, node_dist);
                TrieHash::from_data(&[])
            },
            TrieNodeType::Node256(ref mut data) => {
                node_copy_update_ptrs(&mut data.ptrs, node_dist);
                TrieHash::from_data(&[])
            },
            TrieNodeType::Leaf(ref mut data) => {
                get_node_hash_bytes(data, &vec![])
            },
        };
        Ok(hash)
    }
    
    /// Given a node, and the chr of one of its children, go find the last instance of that child in
    /// the MARF and copy it forward.  Update its ptrs to point to its descendents.
    /// s must point to the block hash in which this node lives, to which the child will be copied.
    fn node_child_copy(s: &mut S, node: &TrieNodeType, chr: u8, c: &mut TrieCursor) -> Result<(TrieNodeType, TrieHash, TriePtr, BlockHeaderHash), Error> {
        test_debug!("Copy to {:?} child {:x} of {:?}", s.tell(), chr, node);

        let cur_block_hash = s.tell();
        let (mut child_node, child_hash, child_ptr, child_dist) = MARF::walk_backptr(s, node, chr, c)?;
        let child_block_hash = s.tell();

        // update child_node with new ptrs and hashes
        s.open(&cur_block_hash, true)?;
        let child_hash = MARF::node_copy_update(s, &mut child_node, child_dist)?;

        // store it in this trie
        s.open(&cur_block_hash, true)?;
        let child_disk_ptr = fseek_end(s)?;
        let child_ptr = TriePtr::new(child_ptr.id(), chr, child_disk_ptr as u32);
        s.write_node(&child_node, child_hash.clone())?;

        test_debug!("Copied child 0x{:02x} to {:?}: ptr={:?} child={:?}", chr, &cur_block_hash, &child_ptr, &child_node);
        Ok((child_node, child_hash, child_ptr, child_block_hash))
    }

    /// Copy the root node from the previous Trie to this Trie, updating its ptrs.
    /// s must point to the target Trie
    fn root_copy(s: &mut S, prev_block_hash: &BlockHeaderHash) -> Result<(), Error> {
        let cur_block_hash = s.tell();
        s.open(prev_block_hash, false)?;
        
        let (mut prev_root, prev_root_hash) = Trie::read_root(s)?;
        let new_root_hash = MARF::node_copy_update(s, &mut prev_root, 1)?;
        
        s.open(&cur_block_hash, true)?;
        let root_ptr = s.root_ptr();
        fseek(s, root_ptr)?;

        s.write_node(&prev_root, new_root_hash)?;
        Ok(())
    }
    
    /// create or open a particular Trie.
    /// If the trie doesn't exist, then extend it from the current Trie and create a root node that
    /// has back pointers to its immediate children in the current trie.
    /// On Ok, s will point to new_bhh and will be open for reading
    fn extend_trie(s: &mut S, new_bhh: &BlockHeaderHash) -> Result<(), Error> {
        let cur_bhh = s.tell();
        if s.num_blocks() == 0 {
            // brand new storage
            s.extend(new_bhh)?;
            let node = TrieNode256::new(&vec![]);
            let hash = get_node_hash(&node, &vec![]);
            s.write_node(&TrieNodeType::Node256(node), hash)
        }
        else {
            // existing storage
            match s.open(new_bhh, true) {
                Ok(_) => {
                    test_debug!("Switch to Trie {:?}", new_bhh);
                    Ok(())
                }
                Err(e) => {
                    match e {
                        Error::NotFoundError => {
                            // bring root forward
                            s.open(&cur_bhh, true)?;
                            s.extend(new_bhh)?;
                            MARF::root_copy(s, &cur_bhh)?;
                            s.open(new_bhh, false)?;
                            let root_ptr = s.root_ptr();
                            fseek(s, root_ptr)?;
                            Ok(())
                        },
                        _ => {
                            Err(e)
                        }
                    }
                }
            }
        }
    }

    /// Walk down this MARF at the given block hash, doing a copy-on-write for intermediate nodes in this block's Trie from any prior Tries.
    /// s must point to the last filled-in Trie -- i.e. block_hash points to the _new_ Trie that is
    /// being filled in.
    fn walk_cow(s: &mut S, block_hash: &BlockHeaderHash, k: &TriePath) -> Result<TrieCursor, Error> {
        MARF::extend_trie(s, block_hash)?;

        let root_ptr = s.root_ptr();
        let mut c = TrieCursor::new(k, root_ptr);

        // walk to insertion point 
        let (mut node, _) = Trie::read_root(s)?;
        let mut node_ptr = TriePtr::new(0,0,0);

        for i in 0..(c.path.len()+1) {
            let next_opt = Trie::walk_from(s, &node, &mut c)?;
            match next_opt {
                Some((next_node_ptr, next_node, _)) => {
                    // keep walking
                    node = next_node;
                    node_ptr = next_node_ptr;
                    continue;
                },
                None => {
                    if c.div() {
                        // we're done -- path diverged.  No node-copying can help us.
                        test_debug!("Path diverged -- we're done.");
                        s.open(block_hash, true)?;
                        fseek(s, node_ptr.ptr() as u64)?;
                        return Ok(c);
                    }
                    else if c.eop() {
                        // we're done
                        test_debug!("Out of path in {:?} -- we're done. Seek to {:?}", s.tell(), &node_ptr);
                        s.open(block_hash, true)?;
                        fseek(s, node_ptr.ptr() as u64)?;
                        return Ok(c);
                    }
                    else {
                        // we're not done with this path.  Either no node exists, or it exists off
                        // of a prior version of the last-visited node.
                        let chr = c.chr().unwrap();     // guaranteed to succeed since we walked some path.
                        match node {
                            TrieNodeType::Leaf(_) => {
                                // at an existing leaf with a different path.
                                // we're done.
                                test_debug!("Existing leaf with different path encountered at {:?} at {:?} -- we're done (not found)", &node_ptr, s.tell());
                                s.open(block_hash, true)?;
                                fseek_end(s)?;
                                return Ok(c);
                            },
                            _ => {}
                        };

                        // at intermediate node whose child is not present in this trie.
                        // bring the child forward and take the step, if possible.
                        s.open(block_hash, true)?;
                        let (next_node, next_node_hash, next_node_ptr, next_node_block_hash) = match MARF::node_child_copy(s, &node, chr, &mut c) {
                            Ok(res) => {
                                res
                            }
                            Err(e) => {
                                match e {
                                    Error::BackptrNotFoundError => {
                                        // no prior version of this node has a ptr for this chr.
                                        // we're done -- target node not found.
                                        test_debug!("BackptrNotFoundError encountered at {:?} -- we're done (not found)", s.tell());
                                        s.open(block_hash, true)?;
                                        fseek_end(s)?;
                                        return Ok(c);
                                    },
                                    _ => {
                                        return Err(e);
                                    }
                                }
                            }
                        };

                        // finish taking the step
                        c.walk_backptr_finish(&next_node_ptr, &next_node_block_hash);
                        
                        node = next_node;
                        node_ptr = next_node_ptr;
                        
                        s.open(block_hash, true)?;
                    }
                }
            }
        }

        test_debug!("Trie has a cycle");
        return Err(Error::CorruptionError("Trie has a cycle".to_string()));
    }


    /// Walk down this MARF at the given block hash, resolving backptrs to previous tries.
    /// Return the cursor and the last node visited
    fn walk(s: &mut S, block_hash: &BlockHeaderHash, k: &TriePath) -> Result<(TrieCursor, TrieNodeType), Error> {
        s.open(block_hash, false)?;

        let root_ptr = s.root_ptr();
        let mut c = TrieCursor::new(k, root_ptr);

        // walk to insertion point 
        let (mut node, _) = Trie::read_root(s)?;
        let mut node_ptr = TriePtr::new(0,0,0);

        for i in 0..(c.path.len()+1) {
            let next_opt = Trie::walk_from(s, &node, &mut c)?;
            match next_opt {
                Some((next_node_ptr, next_node, _)) => {
                    // keep walking
                    node = next_node;
                    node_ptr = next_node_ptr;
                    continue;
                },
                None => {
                    if c.div() {
                        // we're done -- path diverged.  No backptr-walking can help us.
                        test_debug!("Path diverged -- we're done.");
                        return Err(Error::NotFoundError);
                    }
                    else {
                        // we're not done with this path.  Either no node exists, or it exists off
                        // of a prior version of the last-visited node.
                        let chr = c.chr().unwrap();     // guaranteed to succeed since we walked some path.
                        let found_leaf = match node {
                            TrieNodeType::Leaf(ref data) => {
                                if !c.eop() {
                                    // at an existing leaf with a different path.
                                    // we're done.
                                    test_debug!("Existing but different leaf encountered at {:?} at {:?} -- we're done", &node_ptr, s.tell());
                                    return Err(Error::NotFoundError);
                                }
                                else {
                                    // we're done -- we found the leaf
                                    true
                                }
                            },
                            _ => {
                                false
                            }
                        };

                        if found_leaf {
                            return Ok((c, node));
                        }

                        // cursor grabbed a copy of node, but not yet a ptr.
                        // at intermediate node whose child is not present in this trie.
                        // try to shunt to the prior node that has the child itself.
                        let (next_node, next_node_hash, next_node_ptr, next_node_dist) = MARF::walk_backptr(s, &node, chr, &mut c)?;
                       
                        // finish taking the step
                        c.walk_backptr_finish(&next_node_ptr, &s.tell());

                        // keep going
                        node = next_node;
                        node_ptr = next_node_ptr;
                    }
                }
            }
        }
        
        test_debug!("Trie has a cycle");
        return Err(Error::CorruptionError("Trie has a cycle".to_string()));
    }

    pub fn format(s: &mut S, first_block_hash: &BlockHeaderHash) -> Result<(), Error> {
        Trie::format(s, first_block_hash)
    }

    pub fn get(s: &mut S, block_hash: &BlockHeaderHash, k: &TriePath) -> Result<Option<TrieLeaf>, Error> {
        test_debug!("MARF::get({:?}) {:?}", block_hash, k);
        s.open(block_hash, false)?;
        let (c, node) = MARF::walk(s, block_hash, k)?;

        if c.block_hashes.len() + 1 != c.node_ptrs.len() {
            test_debug!("c.block_hashes = {:?}", &c.block_hashes);
            test_debug!("c.node_ptrs = {:?}", c.node_ptrs);
            assert!(false);
        }

        if c.eop() {
            // out of path and reached the end.
            match node {
                TrieNodeType::Leaf(data) => {
                    // found!
                    return Ok(Some(data));
                },
                _ => {
                    // Trie invariant violation -- a full path reached a non-leaf
                    return Err(Error::CorruptionError("Path reached a non-leaf".to_string()));
                }
            }
        }
        else {
            // path didn't match a node 
            test_debug!("MARF get: found nothing at {:?}", k);
            return Ok(None);
        }
    }

    pub fn insert(s: &mut S, block_hash: &BlockHeaderHash, k: &TriePath, v: &TrieLeaf) -> Result<(), Error> {
        let mut value = v.clone();
        let mut c = MARF::walk_cow(s, block_hash, k)?;
        
        if c.block_hashes.len() + 1 != c.node_ptrs.len() {
            test_debug!("c.block_hashes = {:?}", &c.block_hashes);
            test_debug!("c.node_ptrs = {:?}", c.node_ptrs);
            assert!(false);
        }
        
        Trie::add_value(s, &mut c, &mut value)?;
        Trie::update_root_hash(s, &c)?;
        Ok(())
    }

    // TODO: insert batch? (avoid excessive re-hashes)
}


#[derive(Clone)]
pub enum TrieMerkleProofType {
    // chr, node, sibling hashes (depth_1 > 0 implies that a backptr was taken)
    Node4((u8, TrieNode4, [TrieHash; 3])),
    Node16((u8, TrieNode16, [TrieHash; 15])),
    Node48((u8, TrieNode48, [TrieHash; 47])),
    Node256((u8, TrieNode256, [TrieHash; 255])),
    Leaf((u8, TrieLeaf))
}

pub fn hashes_fmt(hashes: &[TrieHash]) -> String {
    let mut strs = vec![];
    for i in 0..hashes.len() {
        strs.push(format!("{:?}", hashes[i]));
    }
    strs.join(",")
}

impl fmt::Debug for TrieMerkleProofType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            TrieMerkleProofType::Node4((ref chr, ref node, ref hashes)) => write!(f, "TrieMerkleProofType::Node4(0x{:02x}, node={:?}, hashes={})", chr, node, hashes_fmt(hashes)),
            TrieMerkleProofType::Node16((ref chr, ref node, ref hashes)) => write!(f, "TrieMerkleProofType::Node16(0x{:02x}, node={:?}, hashes={})", chr, node, hashes_fmt(hashes)),
            TrieMerkleProofType::Node48((ref chr, ref node, ref hashes)) => write!(f, "TrieMerkleProofType::Node48(0x{:02x}, node={:?}, hashes={})", chr, node, hashes_fmt(hashes)),
            TrieMerkleProofType::Node256((ref chr, ref node, ref hashes)) => write!(f, "TrieMerkleProofType::Node256(0x{:02x}, node={:?}, hashes={})", chr, node, hashes_fmt(hashes)),
            TrieMerkleProofType::Leaf((ref chr, ref node)) => write!(f, "TrieMerkleProofType::Leaf(0x{:02x}, node={:?})", chr, node),
        }
    }
}

impl PartialEq for TrieMerkleProofType {
    fn eq(&self, other: &TrieMerkleProofType) -> bool {
        match (self, other) {
            (TrieMerkleProofType::Node4((ref chr, ref node, ref hashes)), TrieMerkleProofType::Node4((ref other_chr, ref other_node, ref other_hashes))) => {
                chr == other_chr && node == other_node && slice_partialeq(hashes, other_hashes)
            },
            (TrieMerkleProofType::Node16((ref chr, ref node, ref hashes)), TrieMerkleProofType::Node16((ref other_chr, ref other_node, ref other_hashes))) => {
                chr == other_chr && node == other_node && slice_partialeq(hashes, other_hashes)
            },
            (TrieMerkleProofType::Node48((ref chr, ref node, ref hashes)), TrieMerkleProofType::Node48((ref other_chr, ref other_node, ref other_hashes))) => {
                chr == other_chr && node == other_node && slice_partialeq(hashes, other_hashes)
            },
            (TrieMerkleProofType::Node256((ref chr, ref node, ref hashes)), TrieMerkleProofType::Node256((ref other_chr, ref other_node, ref other_hashes))) => {
                chr == other_chr && node == other_node && slice_partialeq(hashes, other_hashes)
            },
            (TrieMerkleProofType::Leaf((ref chr, ref node)), TrieMerkleProofType::Leaf((ref other_chr, ref other_node))) => {
                chr == other_chr && node == other_node
            },
            (_, _) => false
        }
    }
}

#[derive(Debug)]
pub struct TrieMerkleProof(Vec<TrieMerkleProofType>);

impl Deref for TrieMerkleProof {
    type Target = Vec<TrieMerkleProofType>;
    fn deref(&self) -> &Vec<TrieMerkleProofType> {
        &self.0
    }
}

impl TrieMerkleProof {
    /// Given a TriePtr to the _currently-visited_ node and the chr of the _previous_ node, calculate a
    /// Merkle proof node.  Include all the children hashes _except_ for the one that corresponds
    /// to the previous node.
    fn ptr_to_proof_node<S: TrieStorage + Seek>(s: &mut S, ptr: &TriePtr, prev_chr: u8) -> Result<TrieMerkleProofType, Error> {
        test_debug!("ptr_to_proof_node: ptr={:?}, prev_chr=0x{:02x}", ptr, prev_chr);
        let (node, _) = Trie::read_node(s, ptr)?;
        let all_hashes = Trie::get_children_hashes(s, &node)?;

        fn make_proof_hashes<T: TrieNode + std::fmt::Debug>(data: &T, all_hashes: &Vec<TrieHash>, chr: u8) -> Vec<TrieHash> {
            let mut hashes = vec![];
            assert!(all_hashes.len() == data.ptrs().len());

            for i in 0..data.ptrs().len() {
                if data.ptrs()[i].id() == TrieNodeID::Empty {
                    hashes.push(TrieHash::from_data(&[]));
                }
                else if data.ptrs()[i].chr() != chr {
                    hashes.push(all_hashes[i].clone());
                }
            }

            if hashes.len() + 1 != data.ptrs().len() {
                panic!(format!("Char 0x{:02x} does not appear in this node", chr));
            }

            hashes
        }
        
        let proof_node = match node {
            TrieNodeType::Leaf(ref data) => {
                TrieMerkleProofType::Leaf((prev_chr, data.clone()))
            },
            TrieNodeType::Node4(ref data) => {
                let hashes = make_proof_hashes(data, &all_hashes, prev_chr);

                let mut hash_slice = [TrieHash::from_data(&[]); 3];
                hash_slice.copy_from_slice(&hashes[0..3]);

                TrieMerkleProofType::Node4((prev_chr, data.clone(), hash_slice))
            },
            TrieNodeType::Node16(ref data) => {
                let hashes = make_proof_hashes(data, &all_hashes, prev_chr);
                
                let mut hash_slice = [TrieHash::from_data(&[]); 15];
                hash_slice.copy_from_slice(&hashes[0..15]);

                TrieMerkleProofType::Node16((prev_chr, data.clone(), hash_slice))
            },
            TrieNodeType::Node48(ref data) => {
                let hashes = make_proof_hashes(data, &all_hashes, prev_chr);
                
                let mut hash_slice = [TrieHash::from_data(&[]); 47];
                hash_slice.copy_from_slice(&hashes[0..47]);

                TrieMerkleProofType::Node48((prev_chr, data.clone(), hash_slice))
            },
            TrieNodeType::Node256(ref data) => {
                let hashes = make_proof_hashes(data, &all_hashes, prev_chr);

                let mut hash_slice = [TrieHash::from_data(&[]); 255];
                hash_slice.copy_from_slice(&hashes[0..255]);

                TrieMerkleProofType::Node256((prev_chr, data.clone(), hash_slice))
            }
        };
        Ok(proof_node)
    }

    fn from_cursor<S: TrieStorage + Seek>(s: &mut S, c: &mut TrieCursor, root_block_header: &BlockHeaderHash) -> Result<TrieMerkleProof, Error> {
        assert!(c.node_ptrs.len() > 0);
        assert!(c.chr().is_some());
        assert_eq!(c.node_ptrs.len(), c.block_hashes.len() + 1);

        let mut ptrs = c.node_ptrs.clone();
        let mut block_hashes = c.block_hashes.clone();
        let mut proof = vec![];
        let mut ptr = TriePtr::new(0,0,0);
        let mut prev_chr = 0;
      
        test_debug!("Cursor to proof: ptrs={:?}", &ptrs);
        test_debug!("Cursor to proof: blocks={:?}", &block_hashes);

        while ptrs.len() > 0 {
            ptr = match ptrs.pop() {
                Some(p) => p,
                None => panic!("out of ptrs")
            };

            match block_hashes.pop() {
                Some(h) => {
                    s.open(&h, false)?;
                }
                None => {
                    // at root
                    assert_eq!(ptrs.len(), 0);
                    s.open(root_block_header, false)?;
                }
            };

            let proof_node = TrieMerkleProof::ptr_to_proof_node(s, &ptr, prev_chr)?;

            test_debug!("Add proof node from {:?} (child 0x{:02x}): {:?}", &ptr, prev_chr, &proof_node);

            proof.push(proof_node);

            if !is_backptr(ptr.id()) {
                prev_chr = ptr.chr();
            }
        }
        
        // must have ended on root 
        let root_ptr = s.root_ptr();
        assert_eq!(ptr, TriePtr::new(TrieNodeID::Node256, 0, root_ptr as u32));
        Ok(TrieMerkleProof(proof))
    }

    pub fn from_path<S: TrieStorage + Seek>(s: &mut S, path: &TriePath) -> Result<TrieMerkleProof, Error> {
        let cur_block_header = s.tell();
        let (mut cursor, node) = MARF::walk(s, &cur_block_header, path)?;
        if cursor.eop() {
            // reached end-of-path.  Make a proof-of-inclusion
            let proof = TrieMerkleProof::from_cursor(s, &mut cursor, &cur_block_header)?;
            Ok(proof)
        }
        else {
            // did not reach end of path -- landed on an intermediate node.
            // TODO: make a proof-of-exclusion
            Err(Error::NotFoundError)
        }
    }

    fn verify_get_hash<T: TrieNode + std::fmt::Debug>(node: &T, hash: &TrieHash, chr: u8, hashes: &[TrieHash], count: usize) -> Option<TrieHash> {
        let mut all_hashes = vec![];
        let mut ih = 0;

        assert!(node.ptrs().len() == count);
        assert!(hashes.len() == 0 || (count > 0 && hashes.len() == count - 1));

        for i in 0..count {
            if node.ptrs()[i].id() != TrieNodeID::Empty && node.ptrs()[i].chr() == chr {
                all_hashes.push(hash.clone());
            }
            else {
                if ih >= hashes.len() {
                    test_debug!("verify_get_hash: {} >= {}", ih, hashes.len());
                    return None;
                }
                else {
                    all_hashes.push(hashes[ih].clone());
                    ih += 1;
                }
            }
        }
        if all_hashes.len() != count {
            test_debug!("verify_get_hash: {} != {}", all_hashes.len(), count);
            return None
        }

        Some(get_node_hash(node, &all_hashes))
    }
    
    pub fn verify(&self, value: &TrieLeaf, root_hash: &TrieHash) -> bool {
        let mut hash = get_node_hash(value, &vec![]);
        let mut prev_hash = hash.clone();
        for j in 0..self.0.len() {
            let hash_opt = match self.0[j] {
                TrieMerkleProofType::Leaf((ref chr, ref node)) => {
                    TrieMerkleProof::verify_get_hash(node, &hash, *chr, &vec![], 0)
                },
                TrieMerkleProofType::Node4((ref chr, ref node, ref hashes)) => {
                    TrieMerkleProof::verify_get_hash(node, &hash, *chr, hashes, 4)
                },
                TrieMerkleProofType::Node16((ref chr, ref node, ref hashes)) => {
                    TrieMerkleProof::verify_get_hash(node, &hash, *chr, hashes, 16)
                },
                TrieMerkleProofType::Node48((ref chr, ref node, ref hashes)) => {
                    TrieMerkleProof::verify_get_hash(node, &hash, *chr, hashes, 48)
                }
                TrieMerkleProofType::Node256((ref chr, ref node, ref hashes)) => {
                    TrieMerkleProof::verify_get_hash(node, &hash, *chr, hashes, 256)
                }
            };
            let mut next_hash = match hash_opt {
                None => {
                    return false;
                }
                Some(h) => h.clone()
            };

            prev_hash = hash;
            hash = next_hash;
        }

        test_debug!("verify: {:?} =?= {:?}", hash, root_hash);
        hash == *root_hash
    }
}


pub fn print_trie<S: TrieStorage + Seek>(s: &mut S) -> () {
    fn space(cnt: usize) -> String {
        let mut ret = vec![];
        for _ in 0..cnt {
            ret.push(" ".to_string());
        }
        ret.join("")
    }

    let root_ptr = s.root_ptr();
    fseek(s, root_ptr).unwrap();

    let mut frontier : Vec<(TrieNodeType, usize)> = vec![];
    let (root, _) = Trie::read_root(s).unwrap();
    frontier.push((root, 0));

    while frontier.len() > 0 {
        let (next, depth) = frontier.pop().unwrap();
        let (ptrs, path_len) = match next {
            TrieNodeType::Leaf(ref leaf_data) => {
                println!("{}{:?}", &space(depth), leaf_data);
                (vec![], leaf_data.path.len())
            },
            TrieNodeType::Node4(ref data) => {
                println!("{}{:?}", &space(depth), data);
                (data.ptrs.to_vec(), data.path.len())
            },
            TrieNodeType::Node16(ref data) => {
                println!("{}{:?}", &space(depth), data);
                (data.ptrs.to_vec(), data.path.len())
            },
            TrieNodeType::Node48(ref data) => {
                println!("{}{:?}", &space(depth), data);
                (data.ptrs.to_vec(), data.path.len())
            },
            TrieNodeType::Node256(ref data) => {
                println!("{}{:?}", &space(depth), data);
                (data.ptrs.to_vec(), data.path.len())
            }
        };
        for ptr in ptrs.iter() {
            if ptr.id() == TrieNodeID::Empty {
                continue;
            }
            if is_backptr(ptr.id()) {
                continue;
            }
            let (child_node, _) = Trie::read_node(s, ptr).unwrap();
            frontier.push((child_node, depth + path_len + 1));
        }
    }
}


#[cfg(test)]
mod test {

    use super::*;

    use std::io::{
        Cursor
    };

    use std::collections::HashMap;
    use std::time::{SystemTime, UNIX_EPOCH};

    pub fn get_epoch_time_ms() -> u128 {
        let start = SystemTime::now();
        let since_the_epoch = start.duration_since(UNIX_EPOCH)
            .expect("Time went backwards");
        return since_the_epoch.as_millis();
    }

    fn dump_trie<S: TrieStorage + Seek>(s: &mut S) -> () {

        test_debug!("\n----- BEGIN TRIE ------");

        fn space(cnt: usize) -> String {
            let mut ret = vec![];
            for _ in 0..cnt {
                ret.push(" ".to_string());
            }
            ret.join("")
        }

        let root_ptr = s.root_ptr();
        fseek(s, root_ptr).unwrap();

        let mut frontier : Vec<(TrieNodeType, usize)> = vec![];
        let (root, _) = Trie::read_root(s).unwrap();
        frontier.push((root, 0));

        while frontier.len() > 0 {
            let (next, depth) = frontier.pop().unwrap();
            let (ptrs, path_len) = match next {
                TrieNodeType::Leaf(ref leaf_data) => {
                    test_debug!("{}{:?}", &space(depth), leaf_data);
                    (vec![], leaf_data.path.len())
                },
                TrieNodeType::Node4(ref data) => {
                    test_debug!("{}{:?}", &space(depth), data);
                    (data.ptrs.to_vec(), data.path.len())
                },
                TrieNodeType::Node16(ref data) => {
                    test_debug!("{}{:?}", &space(depth), data);
                    (data.ptrs.to_vec(), data.path.len())
                },
                TrieNodeType::Node48(ref data) => {
                    test_debug!("{}{:?}", &space(depth), data);
                    (data.ptrs.to_vec(), data.path.len())
                },
                TrieNodeType::Node256(ref data) => {
                    test_debug!("{}{:?}", &space(depth), data);
                    (data.ptrs.to_vec(), data.path.len())
                }
            };
            for ptr in ptrs.iter() {
                if ptr.id() == TrieNodeID::Empty {
                    continue;
                }
                if !is_backptr(ptr.id()) {
                    let (child_node, _) = Trie::read_node(s, ptr).unwrap();
                    frontier.push((child_node, depth + path_len + 1));
                }
            }
        }
        
        test_debug!("----- END TRIE ------\n");
    }

    // ram-disk trie (for testing)
    pub struct TrieIOBuffer {
        bufs: HashMap<BlockHeaderHash, Cursor<Vec<u8>>>,
        block_header: BlockHeaderHash,
        readonly: bool,
        
        read_count: u64,
        read_backptr_count: u64,
        read_node_count: u64,
        read_leaf_count: u64,

        write_count: u64,
        write_backptr_count: u64,
        write_node_count: u64,
        write_leaf_count: u64,
    }

    impl TrieIOBuffer {
        pub fn new(buf: Cursor<Vec<u8>>) -> TrieIOBuffer {
            let mut ret = TrieIOBuffer {
                bufs: HashMap::new(),
                block_header: BlockHeaderHash([0u8; 32]),
                readonly: false,
                
                read_count: 0,
                read_backptr_count: 0,
                read_node_count: 0,
                read_leaf_count: 0,

                write_count: 0,
                write_backptr_count: 0,
                write_node_count: 0,
                write_leaf_count: 0
            };
            ret.bufs.insert(ret.block_header.clone(), buf);
            ret
        }

        pub fn stats(&mut self) -> (u64, u64) {
            let r = self.read_count;
            let w = self.write_count;
            self.read_count = 0;
            self.write_count = 0;
            (r, w)
        }
        
        pub fn node_stats(&mut self) -> (u64, u64, u64, u64) {
            let nr = self.read_node_count;
            let br = self.read_backptr_count;
            let nw = self.write_node_count;
            let bw = self.write_backptr_count;

            self.read_node_count = 0;
            self.read_backptr_count = 0;
            self.write_node_count = 0;
            self.write_backptr_count = 0;

            (nr, br, nw, bw)
        }

        pub fn leaf_stats(&mut self) -> (u64, u64) {
            let lr = self.read_leaf_count;
            let lw = self.write_leaf_count;

            self.read_leaf_count = 0;
            self.write_leaf_count = 0;

            (lr, lw)
        }
    }

    impl TrieStorage for TrieIOBuffer {
        fn extend(&mut self, bhh: &BlockHeaderHash) -> Result<(), Error> {
            if self.bufs.contains_key(bhh) {
                return Err(Error::ExistsError);
            }
            test_debug!("Extend to {:?}", bhh);
            self.bufs.insert((*bhh).clone(), Cursor::new(vec![]));
            self.block_header = bhh.clone();
            self.readonly = false;
            Ok(())
        }

        fn open(&mut self, bhh: &BlockHeaderHash, readwrite: bool) -> Result<(), Error> {
            if !self.bufs.contains_key(bhh) {
                test_debug!("Block not found: {:?}", bhh);
                return Err(Error::NotFoundError);
            }
            self.block_header = bhh.clone();
            self.readonly = !readwrite;
            Ok(())
        }
        
        fn tell(&self) -> BlockHeaderHash {
            self.block_header.clone()
        }

        fn block_walk(&self, back_block: u32) -> Result<BlockHeaderHash, Error> {
            panic!("not implemented for trieiobuffer");
        }
        
        fn root_ptr(&self) -> u64 { 0 }

        fn readwrite(&self) -> bool {
            !self.readonly
        }

        fn format(&mut self) -> Result<(), Error> {
            if self.readonly {
                test_debug!("Read-only!");
                return Err(Error::ReadOnlyError);
            }

            self.bufs.clear();
            Ok(())
        }

        fn read_node_hash_bytes(&mut self, ptr: &TriePtr, hash_buf: &mut Vec<u8>) -> Result<(), Error> {
            match self.bufs.get_mut(&self.block_header) {
                Some(ref mut buf) => {
                    read_node_hash_bytes(buf, ptr, hash_buf)
                }
                None => {
                    test_debug!("Node hash not found: {:?}", ptr);
                    Err(Error::NotFoundError)
                }
            }
        }

        fn read_node(&mut self, ptr: &TriePtr) -> Result<(TrieNodeType, TrieHash), Error> {
            test_debug!("read_node({:?}): {:?}", &self.block_header, ptr);
            
            self.read_count += 1;
            if is_backptr(ptr.id()) {
                self.read_backptr_count += 1;
            }
            else if ptr.id() == TrieNodeID::Leaf {
                self.read_leaf_count += 1;
            }
            else {
                self.read_node_count += 1;
            }

            let clear_ptr = TriePtr::new(clear_backptr(ptr.id()), ptr.chr(), ptr.ptr());

            match self.bufs.get_mut(&self.block_header) {
                Some(ref mut buf) => {
                    read_nodetype(buf, &clear_ptr)
                },
                None => {
                    test_debug!("Node not found: {:?}", &clear_ptr);
                    Err(Error::NotFoundError)
                }
            }
        }
        
        fn write_node(&mut self, node: &TrieNodeType, hash: TrieHash) -> Result<(), Error> {
            if self.readonly {
                test_debug!("Read-only!");
                return Err(Error::ReadOnlyError);
            }

            let disk_ptr = ftell(self)?;
            test_debug!("write_node({:?}): at {}: {:?} {:?}", &self.block_header, disk_ptr, &hash, node);
            
            self.write_count += 1;
            match node {
                TrieNodeType::Leaf(ref data) => {
                    self.write_leaf_count += 1;
                },
                TrieNodeType::Node4(ref data) => {
                    self.write_node_count += 1;
                }
                TrieNodeType::Node16(ref data) => {
                    self.write_node_count += 1;
                }
                TrieNodeType::Node48(ref data) => {
                    self.write_node_count += 1;
                }
                TrieNodeType::Node256(ref data) => {
                    self.write_node_count += 1;
                },
            }

            match self.bufs.get_mut(&self.block_header) {
                Some(ref mut buf) => {
                    match node {
                        TrieNodeType::Leaf(ref data) => write_node_bytes(buf, data, hash),
                        TrieNodeType::Node4(ref data) => write_node_bytes(buf, data, hash),
                        TrieNodeType::Node16(ref data) => write_node_bytes(buf, data, hash),
                        TrieNodeType::Node48(ref data) => write_node_bytes(buf, data, hash),
                        TrieNodeType::Node256(ref data) => write_node_bytes(buf, data, hash),
                    }?;
                    Ok(())
                },
                None => {
                    test_debug!("Block data does not exist for {:?}", &self.block_header);
                    Err(Error::NotFoundError)
                }
            }
        }
        
        fn flush(&mut self) -> Result<(), Error> {
            Ok(())
        }

        fn num_blocks(&self) -> usize {
            self.bufs.len()
        }
    }

    impl Seek for TrieIOBuffer {
        fn seek(&mut self, pos: SeekFrom) -> io::Result<u64> {
            match self.bufs.get_mut(&self.block_header) {
                Some(ref mut buf) => {
                    buf.seek(pos)
                },
                None => {
                    Err(io::Error::new(io::ErrorKind::Other, Error::NotFoundError))
                }
            }
        }
    }

    fn merkle_test<S: TrieStorage + Seek>(s: &mut S, path: &Vec<u8>, value: &Vec<u8>) -> () {
        let (_, root_hash) = Trie::read_root(s).unwrap();
        let triepath = TriePath::from_bytes(&path[..]).unwrap();
        let value_leaf = TrieLeaf::new(&vec![], &value);

        let block_header = BlockHeaderHash([0u8; 32]);
        s.open(&block_header, false).unwrap();

        let proof = TrieMerkleProof::from_path(s, &triepath).unwrap();
        assert!(proof.verify(&value_leaf, &root_hash));
    }
    
    fn merkle_test_marf<S: TrieStorage + Seek>(s: &mut S, header: &BlockHeaderHash, path: &Vec<u8>, value: &Vec<u8>) -> () {

        test_debug!("---------");
        test_debug!("MARF merkle prove: merkle_test_marf({:?}, {:?}, {:?})?", header, path, value);
        test_debug!("---------");

        s.open(header, false).unwrap();
        let (_, root_hash) = Trie::read_root(s).unwrap();
        let triepath = TriePath::from_bytes(&path[..]).unwrap();
        let value_leaf = TrieLeaf::new(&vec![], &value);
        let proof = TrieMerkleProof::from_path(s, &triepath).unwrap();

        test_debug!("---------");
        test_debug!("MARF merkle verify: {:?}", &proof);
        test_debug!("---------");

        assert!(proof.verify(&value_leaf, &root_hash));
    }

    #[test]
    fn trieptr_to_bytes() {
        let mut t = TriePtr::new(0x11, 0x22, 0x33445566);
        t.back_block = 0x778899aa;

        let t_bytes = vec![0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xaa];
        let mut buf = Vec::with_capacity(TRIEPTR_SIZE);
        t.to_bytes(&mut buf);
        assert_eq!(buf, t_bytes);
        assert_eq!(TriePtr::from_bytes(&t_bytes[..]), t);
    }

    #[test]
    fn trie_node4_to_bytes() {
        let mut node4 = TrieNode4::new(&vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19]);
        for i in 0..3 {
            assert!(node4.insert(&TriePtr::new(TrieNodeID::Node16, (i+1) as u8, (i+2) as u32)));
        }
        let node4_bytes = vec![
            // node ID
            TrieNodeID::Node4,
            // ptrs (4)
            TrieNodeID::Node16, 0x01, 0x00, 0x00, 0x00, 0x2, 0x00, 0x00, 0x00, 0x00,
            TrieNodeID::Node16, 0x02, 0x00, 0x00, 0x00, 0x3, 0x00, 0x00, 0x00, 0x00,
            TrieNodeID::Node16, 0x03, 0x00, 0x00, 0x00, 0x4, 0x00, 0x00, 0x00, 0x00,
            TrieNodeID::Empty, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            // path length 
            0x14,
            // path 
            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10, 0x11, 0x12, 0x13
        ];
        let mut node4_stream = Cursor::new(node4_bytes.clone());
        let mut buf = Vec::with_capacity(node4_bytes.len());
        node4.to_bytes(&mut buf);
        assert_eq!(buf, node4_bytes);
        assert_eq!(node4.byte_len(), node4_bytes.len());
        assert_eq!(TrieNode4::from_bytes(&mut node4_stream).unwrap(), node4);
    }

    #[test]
    fn trie_node4_to_consensus_bytes() {
        let mut node4 = TrieNode4::new(&vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19]);
        for i in 0..3 {
            assert!(node4.insert(&TriePtr::new(TrieNodeID::Node16, (i+1) as u8, (i+2) as u32)));
        }
        let node4_bytes = vec![
            // node ID
            TrieNodeID::Node4,
            // ptrs (4)
            TrieNodeID::Node16, 0x01, 0, 0, 0, 0, 
            TrieNodeID::Node16, 0x02, 0, 0, 0, 0, 
            TrieNodeID::Node16, 0x03, 0, 0, 0, 0, 
            TrieNodeID::Empty, 0x00, 0, 0, 0, 0, 
            // path length 
            0x14,
            // path 
            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10, 0x11, 0x12, 0x13
        ];
        let node4_stream = Cursor::new(node4_bytes.clone());
        
        let mut buf = Vec::with_capacity(node4_bytes.len());
        node4.to_consensus_bytes(&mut buf);
        assert_eq!(buf, node4_bytes);
    }
    
    #[test]
    fn trie_node16_to_bytes() {
        let mut node16 = TrieNode16::new(&vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19]);
        for i in 0..15 {
            assert!(node16.insert(&TriePtr::new(TrieNodeID::Node48, (i+1) as u8, (i+2) as u32)));
        }
        let node16_bytes = vec![
            // node ID
            TrieNodeID::Node16,
            // ptrs (16)
            TrieNodeID::Node48, 0x01, 0x00, 0x00, 0x00, 0x02, 0x00, 0x00, 0x00, 0x00,
            TrieNodeID::Node48, 0x02, 0x00, 0x00, 0x00, 0x03, 0x00, 0x00, 0x00, 0x00,
            TrieNodeID::Node48, 0x03, 0x00, 0x00, 0x00, 0x04, 0x00, 0x00, 0x00, 0x00,
            TrieNodeID::Node48, 0x04, 0x00, 0x00, 0x00, 0x05, 0x00, 0x00, 0x00, 0x00,
            TrieNodeID::Node48, 0x05, 0x00, 0x00, 0x00, 0x06, 0x00, 0x00, 0x00, 0x00,
            TrieNodeID::Node48, 0x06, 0x00, 0x00, 0x00, 0x07, 0x00, 0x00, 0x00, 0x00,
            TrieNodeID::Node48, 0x07, 0x00, 0x00, 0x00, 0x08, 0x00, 0x00, 0x00, 0x00,
            TrieNodeID::Node48, 0x08, 0x00, 0x00, 0x00, 0x09, 0x00, 0x00, 0x00, 0x00,
            TrieNodeID::Node48, 0x09, 0x00, 0x00, 0x00, 0x0a, 0x00, 0x00, 0x00, 0x00,
            TrieNodeID::Node48, 0x0a, 0x00, 0x00, 0x00, 0x0b, 0x00, 0x00, 0x00, 0x00,
            TrieNodeID::Node48, 0x0b, 0x00, 0x00, 0x00, 0x0c, 0x00, 0x00, 0x00, 0x00,
            TrieNodeID::Node48, 0x0c, 0x00, 0x00, 0x00, 0x0d, 0x00, 0x00, 0x00, 0x00,
            TrieNodeID::Node48, 0x0d, 0x00, 0x00, 0x00, 0x0e, 0x00, 0x00, 0x00, 0x00,
            TrieNodeID::Node48, 0x0e, 0x00, 0x00, 0x00, 0x0f, 0x00, 0x00, 0x00, 0x00,
            TrieNodeID::Node48, 0x0f, 0x00, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x00,
            TrieNodeID::Empty, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            // path length 
            0x14,
            // path 
            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10, 0x11, 0x12, 0x13
        ];
        let mut node16_stream = Cursor::new(node16_bytes.clone());
        let mut buf = Vec::with_capacity(node16_bytes.len());
        node16.to_bytes(&mut buf);
        assert_eq!(buf, node16_bytes);
        assert_eq!(node16.byte_len(), node16_bytes.len());
        assert_eq!(TrieNode16::from_bytes(&mut node16_stream).unwrap(), node16);
    }
    
    #[test]
    fn trie_node16_to_consensus_bytes() {
        let mut node16 = TrieNode16::new(&vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19]);
        for i in 0..15 {
            assert!(node16.insert(&TriePtr::new(TrieNodeID::Node48, (i+1) as u8, (i+2) as u32)));
        }
        let node16_bytes = vec![
            // node ID
            TrieNodeID::Node16,
            // ptrs (16)
            TrieNodeID::Node48, 0x01, 0, 0, 0, 0, 
            TrieNodeID::Node48, 0x02, 0, 0, 0, 0, 
            TrieNodeID::Node48, 0x03, 0, 0, 0, 0, 
            TrieNodeID::Node48, 0x04, 0, 0, 0, 0, 
            TrieNodeID::Node48, 0x05, 0, 0, 0, 0, 
            TrieNodeID::Node48, 0x06, 0, 0, 0, 0, 
            TrieNodeID::Node48, 0x07, 0, 0, 0, 0, 
            TrieNodeID::Node48, 0x08, 0, 0, 0, 0, 
            TrieNodeID::Node48, 0x09, 0, 0, 0, 0, 
            TrieNodeID::Node48, 0x0a, 0, 0, 0, 0, 
            TrieNodeID::Node48, 0x0b, 0, 0, 0, 0, 
            TrieNodeID::Node48, 0x0c, 0, 0, 0, 0, 
            TrieNodeID::Node48, 0x0d, 0, 0, 0, 0, 
            TrieNodeID::Node48, 0x0e, 0, 0, 0, 0, 
            TrieNodeID::Node48, 0x0f, 0, 0, 0, 0, 
            TrieNodeID::Empty, 0x00, 0, 0, 0, 0, 
            // path length 
            0x14,
            // path 
            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10, 0x11, 0x12, 0x13
        ];
        let node16_stream = Cursor::new(node16_bytes.clone());
        let mut buf = Vec::with_capacity(node16_bytes.len());
        node16.to_consensus_bytes(&mut buf);
        assert_eq!(buf, node16_bytes);
    }

    #[test]
    fn trie_node48_to_bytes() {
        let mut node48 = TrieNode48::new(&vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19]);
        for i in 0..47 {
            assert!(node48.insert(&TriePtr::new(TrieNodeID::Node256, (i+1) as u8, (i+2) as u32)));
        }

        let node48_bytes = vec![
            // node ID
            TrieNodeID::Node48,
            // ptrs (48)
            TrieNodeID::Node256, 0x01, 0x00, 0x00, 0x00, 0x02, 0x00, 0x00, 0x00, 0x00,
            TrieNodeID::Node256, 0x02, 0x00, 0x00, 0x00, 0x03, 0x00, 0x00, 0x00, 0x00,
            TrieNodeID::Node256, 0x03, 0x00, 0x00, 0x00, 0x04, 0x00, 0x00, 0x00, 0x00,
            TrieNodeID::Node256, 0x04, 0x00, 0x00, 0x00, 0x05, 0x00, 0x00, 0x00, 0x00,
            TrieNodeID::Node256, 0x05, 0x00, 0x00, 0x00, 0x06, 0x00, 0x00, 0x00, 0x00,
            TrieNodeID::Node256, 0x06, 0x00, 0x00, 0x00, 0x07, 0x00, 0x00, 0x00, 0x00,
            TrieNodeID::Node256, 0x07, 0x00, 0x00, 0x00, 0x08, 0x00, 0x00, 0x00, 0x00,
            TrieNodeID::Node256, 0x08, 0x00, 0x00, 0x00, 0x09, 0x00, 0x00, 0x00, 0x00,
            TrieNodeID::Node256, 0x09, 0x00, 0x00, 0x00, 0x0a, 0x00, 0x00, 0x00, 0x00,
            TrieNodeID::Node256, 0x0a, 0x00, 0x00, 0x00, 0x0b, 0x00, 0x00, 0x00, 0x00,
            TrieNodeID::Node256, 0x0b, 0x00, 0x00, 0x00, 0x0c, 0x00, 0x00, 0x00, 0x00,
            TrieNodeID::Node256, 0x0c, 0x00, 0x00, 0x00, 0x0d, 0x00, 0x00, 0x00, 0x00,
            TrieNodeID::Node256, 0x0d, 0x00, 0x00, 0x00, 0x0e, 0x00, 0x00, 0x00, 0x00,
            TrieNodeID::Node256, 0x0e, 0x00, 0x00, 0x00, 0x0f, 0x00, 0x00, 0x00, 0x00,
            TrieNodeID::Node256, 0x0f, 0x00, 0x00, 0x00, 0x10, 0x00, 0x00, 0x00, 0x00,
            TrieNodeID::Node256, 0x10, 0x00, 0x00, 0x00, 0x11, 0x00, 0x00, 0x00, 0x00,
            TrieNodeID::Node256, 0x11, 0x00, 0x00, 0x00, 0x12, 0x00, 0x00, 0x00, 0x00,
            TrieNodeID::Node256, 0x12, 0x00, 0x00, 0x00, 0x13, 0x00, 0x00, 0x00, 0x00,
            TrieNodeID::Node256, 0x13, 0x00, 0x00, 0x00, 0x14, 0x00, 0x00, 0x00, 0x00,
            TrieNodeID::Node256, 0x14, 0x00, 0x00, 0x00, 0x15, 0x00, 0x00, 0x00, 0x00,
            TrieNodeID::Node256, 0x15, 0x00, 0x00, 0x00, 0x16, 0x00, 0x00, 0x00, 0x00,
            TrieNodeID::Node256, 0x16, 0x00, 0x00, 0x00, 0x17, 0x00, 0x00, 0x00, 0x00,
            TrieNodeID::Node256, 0x17, 0x00, 0x00, 0x00, 0x18, 0x00, 0x00, 0x00, 0x00,
            TrieNodeID::Node256, 0x18, 0x00, 0x00, 0x00, 0x19, 0x00, 0x00, 0x00, 0x00,
            TrieNodeID::Node256, 0x19, 0x00, 0x00, 0x00, 0x1a, 0x00, 0x00, 0x00, 0x00,
            TrieNodeID::Node256, 0x1a, 0x00, 0x00, 0x00, 0x1b, 0x00, 0x00, 0x00, 0x00,
            TrieNodeID::Node256, 0x1b, 0x00, 0x00, 0x00, 0x1c, 0x00, 0x00, 0x00, 0x00,
            TrieNodeID::Node256, 0x1c, 0x00, 0x00, 0x00, 0x1d, 0x00, 0x00, 0x00, 0x00,
            TrieNodeID::Node256, 0x1d, 0x00, 0x00, 0x00, 0x1e, 0x00, 0x00, 0x00, 0x00,
            TrieNodeID::Node256, 0x1e, 0x00, 0x00, 0x00, 0x1f, 0x00, 0x00, 0x00, 0x00,
            TrieNodeID::Node256, 0x1f, 0x00, 0x00, 0x00, 0x20, 0x00, 0x00, 0x00, 0x00,
            TrieNodeID::Node256, 0x20, 0x00, 0x00, 0x00, 0x21, 0x00, 0x00, 0x00, 0x00,
            TrieNodeID::Node256, 0x21, 0x00, 0x00, 0x00, 0x22, 0x00, 0x00, 0x00, 0x00,
            TrieNodeID::Node256, 0x22, 0x00, 0x00, 0x00, 0x23, 0x00, 0x00, 0x00, 0x00,
            TrieNodeID::Node256, 0x23, 0x00, 0x00, 0x00, 0x24, 0x00, 0x00, 0x00, 0x00,
            TrieNodeID::Node256, 0x24, 0x00, 0x00, 0x00, 0x25, 0x00, 0x00, 0x00, 0x00,
            TrieNodeID::Node256, 0x25, 0x00, 0x00, 0x00, 0x26, 0x00, 0x00, 0x00, 0x00,
            TrieNodeID::Node256, 0x26, 0x00, 0x00, 0x00, 0x27, 0x00, 0x00, 0x00, 0x00,
            TrieNodeID::Node256, 0x27, 0x00, 0x00, 0x00, 0x28, 0x00, 0x00, 0x00, 0x00,
            TrieNodeID::Node256, 0x28, 0x00, 0x00, 0x00, 0x29, 0x00, 0x00, 0x00, 0x00,
            TrieNodeID::Node256, 0x29, 0x00, 0x00, 0x00, 0x2a, 0x00, 0x00, 0x00, 0x00,
            TrieNodeID::Node256, 0x2a, 0x00, 0x00, 0x00, 0x2b, 0x00, 0x00, 0x00, 0x00,
            TrieNodeID::Node256, 0x2b, 0x00, 0x00, 0x00, 0x2c, 0x00, 0x00, 0x00, 0x00,
            TrieNodeID::Node256, 0x2c, 0x00, 0x00, 0x00, 0x2d, 0x00, 0x00, 0x00, 0x00,
            TrieNodeID::Node256, 0x2d, 0x00, 0x00, 0x00, 0x2e, 0x00, 0x00, 0x00, 0x00,
            TrieNodeID::Node256, 0x2e, 0x00, 0x00, 0x00, 0x2f, 0x00, 0x00, 0x00, 0x00,
            TrieNodeID::Node256, 0x2f, 0x00, 0x00, 0x00, 0x30, 0x00, 0x00, 0x00, 0x00,
            TrieNodeID::Empty, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            // indexes (256)
            255,  0,  1,  2,  3,  4,  5,  6,
             7,  8,  9, 10, 11, 12, 13, 14,
            15, 16, 17, 18, 19, 20, 21, 22,
            23, 24, 25, 26, 27, 28, 29, 30,
            31, 32, 33, 34, 35, 36, 37, 38,
            39, 40, 41, 42, 43, 44, 45, 46,
            255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255,
            // path len
            0x14,
            // path 
            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10, 0x11, 0x12, 0x13
        ];
        let mut node48_stream = Cursor::new(node48_bytes.clone());

        let mut buf = Vec::with_capacity(node48_bytes.len());
        node48.to_bytes(&mut buf);
        assert_eq!(buf, node48_bytes);
        assert_eq!(node48.byte_len(), node48_bytes.len());
        assert_eq!(TrieNode48::from_bytes(&mut node48_stream).unwrap(), node48);
    }

    #[test]
    fn trie_node48_to_consensus_bytes() {
        let mut node48 = TrieNode48::new(&vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19]);
        for i in 0..47 {
            assert!(node48.insert(&TriePtr::new(TrieNodeID::Node256, (i+1) as u8, (i+2) as u32)));
        }
        let node48_bytes = vec![
            // node ID
            TrieNodeID::Node48,
            // ptrs (48)
            TrieNodeID::Node256, 0x01, 0, 0, 0, 0,
            TrieNodeID::Node256, 0x02, 0, 0, 0, 0,
            TrieNodeID::Node256, 0x03, 0, 0, 0, 0,
            TrieNodeID::Node256, 0x04, 0, 0, 0, 0,
            TrieNodeID::Node256, 0x05, 0, 0, 0, 0,
            TrieNodeID::Node256, 0x06, 0, 0, 0, 0,
            TrieNodeID::Node256, 0x07, 0, 0, 0, 0,
            TrieNodeID::Node256, 0x08, 0, 0, 0, 0,
            TrieNodeID::Node256, 0x09, 0, 0, 0, 0,
            TrieNodeID::Node256, 0x0a, 0, 0, 0, 0,
            TrieNodeID::Node256, 0x0b, 0, 0, 0, 0,
            TrieNodeID::Node256, 0x0c, 0, 0, 0, 0,
            TrieNodeID::Node256, 0x0d, 0, 0, 0, 0,
            TrieNodeID::Node256, 0x0e, 0, 0, 0, 0,
            TrieNodeID::Node256, 0x0f, 0, 0, 0, 0,
            TrieNodeID::Node256, 0x10, 0, 0, 0, 0,
            TrieNodeID::Node256, 0x11, 0, 0, 0, 0,
            TrieNodeID::Node256, 0x12, 0, 0, 0, 0,
            TrieNodeID::Node256, 0x13, 0, 0, 0, 0,
            TrieNodeID::Node256, 0x14, 0, 0, 0, 0,
            TrieNodeID::Node256, 0x15, 0, 0, 0, 0,
            TrieNodeID::Node256, 0x16, 0, 0, 0, 0,
            TrieNodeID::Node256, 0x17, 0, 0, 0, 0,
            TrieNodeID::Node256, 0x18, 0, 0, 0, 0,
            TrieNodeID::Node256, 0x19, 0, 0, 0, 0,
            TrieNodeID::Node256, 0x1a, 0, 0, 0, 0,
            TrieNodeID::Node256, 0x1b, 0, 0, 0, 0,
            TrieNodeID::Node256, 0x1c, 0, 0, 0, 0,
            TrieNodeID::Node256, 0x1d, 0, 0, 0, 0,
            TrieNodeID::Node256, 0x1e, 0, 0, 0, 0,
            TrieNodeID::Node256, 0x1f, 0, 0, 0, 0,
            TrieNodeID::Node256, 0x20, 0, 0, 0, 0,
            TrieNodeID::Node256, 0x21, 0, 0, 0, 0,
            TrieNodeID::Node256, 0x22, 0, 0, 0, 0,
            TrieNodeID::Node256, 0x23, 0, 0, 0, 0,
            TrieNodeID::Node256, 0x24, 0, 0, 0, 0,
            TrieNodeID::Node256, 0x25, 0, 0, 0, 0,
            TrieNodeID::Node256, 0x26, 0, 0, 0, 0,
            TrieNodeID::Node256, 0x27, 0, 0, 0, 0,
            TrieNodeID::Node256, 0x28, 0, 0, 0, 0,
            TrieNodeID::Node256, 0x29, 0, 0, 0, 0,
            TrieNodeID::Node256, 0x2a, 0, 0, 0, 0,
            TrieNodeID::Node256, 0x2b, 0, 0, 0, 0,
            TrieNodeID::Node256, 0x2c, 0, 0, 0, 0,
            TrieNodeID::Node256, 0x2d, 0, 0, 0, 0,
            TrieNodeID::Node256, 0x2e, 0, 0, 0, 0,
            TrieNodeID::Node256, 0x2f, 0, 0, 0, 0,
            TrieNodeID::Empty, 0x00, 0, 0, 0, 0,
            // indexes (256)
            255,  0,  1,  2,  3,  4,  5,  6,
             7,  8,  9, 10, 11, 12, 13, 14,
            15, 16, 17, 18, 19, 20, 21, 22,
            23, 24, 25, 26, 27, 28, 29, 30,
            31, 32, 33, 34, 35, 36, 37, 38,
            39, 40, 41, 42, 43, 44, 45, 46,
            255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255,
            255, 255, 255, 255, 255, 255, 255, 255,
            // path len
            0x14,
            // path 
            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10, 0x11, 0x12, 0x13
        ];
        let node48_stream = Cursor::new(node48_bytes.clone());
        let mut buf = Vec::with_capacity(node48_bytes.len());
        node48.to_consensus_bytes(&mut buf);
        assert_eq!(buf, node48_bytes);
    }
    
    #[test]
    fn trie_node256_to_bytes() {
        let mut node256 = TrieNode256::new(&vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19]);
        for i in 0..255 {
            assert!(node256.insert(&TriePtr::new(TrieNodeID::Node256, i as u8, (i+2) % 256)));
        }

        let mut node256_bytes = vec![
            // node ID
            TrieNodeID::Node256
        ];
        // ptrs (256)
        for i in 0..255 {
            node256_bytes.append(&mut vec![
                TrieNodeID::Node256, i as u8, 0, 0, 0, (((i+2) % 256) as u8), 0, 0, 0, 0
            ]);
        }
        // last ptr is empty 
        node256_bytes.append(&mut vec![
            TrieNodeID::Empty, 0, 0, 0, 0, 0, 0, 0, 0, 0
        ]);
        // path 
        node256_bytes.append(&mut vec![
            // path len
            0x14,
            // path 
            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10, 0x11, 0x12, 0x13
        ]);

        let mut node256_stream = Cursor::new(node256_bytes.clone());

        let mut buf = Vec::with_capacity(node256_bytes.len());
        node256.to_bytes(&mut buf);
        assert_eq!(buf, node256_bytes);
        assert_eq!(node256.byte_len(), node256_bytes.len());
        assert_eq!(TrieNode256::from_bytes(&mut node256_stream).unwrap(), node256);
    }
    
    #[test]
    fn trie_node256_to_consensus_bytes() {
        let mut node256 = TrieNode256::new(&vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19]);
        for i in 0..255 {
            assert!(node256.insert(&TriePtr::new(TrieNodeID::Node256, i as u8, (i+2) % 256)));
        }

        let mut node256_bytes = vec![
            // node ID
            TrieNodeID::Node256
        ];
        // ptrs (256)
        for i in 0..255 {
            node256_bytes.append(&mut vec![
                TrieNodeID::Node256, i as u8, 0, 0, 0, 0
            ]);
        }
        // last ptr is empty 
        node256_bytes.append(&mut vec![
            TrieNodeID::Empty, 0, 0, 0, 0, 0
        ]);
        // path 
        node256_bytes.append(&mut vec![
            // path len
            0x14,
            // path 
            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10, 0x11, 0x12, 0x13
        ]);

        let node256_stream = Cursor::new(node256_bytes.clone());
        let mut buf = Vec::with_capacity(node256_bytes.len());
        node256.to_consensus_bytes(&mut buf);
        assert_eq!(buf, node256_bytes);
    }

    #[test]
    fn trie_leaf_to_bytes() {
        let leaf = TrieLeaf::new(
            &vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19], 
            &vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39]
        );
        let leaf_bytes = vec![
                // node ID
                TrieNodeID::Leaf,
                // path len
                0x14,
                // path
                0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,
                // reserved
                0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,
                // backptr
                TrieNodeID::Leaf,0,0,0,0,0,0,0,0,0,0
            ];

        let mut buf = Vec::with_capacity(leaf_bytes.len());
        leaf.to_bytes(&mut buf);

        assert_eq!(buf, leaf_bytes);
        assert_eq!(leaf.byte_len(), buf.len());
    }

    #[test]
    fn read_write_node4() {
        let mut node4 = TrieNode4::new(&vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19]);
        for i in 0..3 {
            assert!(node4.insert(&TriePtr::new(TrieNodeID::Node16, (i+1) as u8, (i+2) as u32)));
        }
        
        let f = Cursor::new(vec![]);
        let mut cursor = TrieIOBuffer::new(f);
        let hash = TrieHash::from_data(&[0u8; 32]);
        let wres = Trie::write_nodetype(&mut cursor, &TrieNodeType::Node4(node4.clone()), hash.clone());
        assert!(wres.is_ok());

        fseek(&mut cursor, 0).unwrap();
        let rres = Trie::read_node(&mut cursor, &TriePtr::new(TrieNodeID::Node4, 0, 0));
        
        assert!(rres.is_ok());
        assert_eq!(rres.unwrap(), (TrieNodeType::Node4(node4.clone()), hash));
    }
    
    #[test]
    fn read_write_node16() {
        let mut node16 = TrieNode16::new(&vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19]);
        for i in 0..16 {
            assert!(node16.insert(&TriePtr::new(TrieNodeID::Node48, (i+1) as u8, (i+2) as u32)));
        }
        let f = Cursor::new(vec![]);
        let mut cursor = TrieIOBuffer::new(f);
        let hash = TrieHash::from_data(&[0u8; 32]);
        let wres = Trie::write_nodetype(&mut cursor, &TrieNodeType::Node16(node16.clone()), hash.clone());
        assert!(wres.is_ok());

        fseek(&mut cursor, 0).unwrap();
        let rres = Trie::read_node(&mut cursor, &TriePtr::new(TrieNodeID::Node16, 0, 0));
        
        assert!(rres.is_ok());
        assert_eq!(rres.unwrap(), (TrieNodeType::Node16(node16.clone()), hash));
    }
    

    #[test]
    fn read_write_node48() {
        let mut node48 = TrieNode48::new(&vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19]);
        for i in 0..48 {
            assert!(node48.insert(&TriePtr::new(TrieNodeID::Node256, (i+1) as u8, (i+2) as u32)));
        }
        let f = Cursor::new(vec![]);
        let mut cursor = TrieIOBuffer::new(f);
        let hash = TrieHash::from_data(&[0u8; 32]);
        let wres = Trie::write_nodetype(&mut cursor, &TrieNodeType::Node48(node48.clone()), hash.clone());
        assert!(wres.is_ok());

        fseek(&mut cursor, 0).unwrap();
        let rres = Trie::read_node(&mut cursor, &TriePtr::new(TrieNodeID::Node48, 0, 0));
        
        assert!(rres.is_ok());
        assert_eq!(rres.unwrap(), (TrieNodeType::Node48(node48.clone()), hash));
    }
    
    #[test]
    fn read_write_node256() {
        let mut node256 = TrieNode256::new(&vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19]);
        for i in 0..256 {
            assert!(node256.insert(&TriePtr::new(TrieNodeID::Node256, (i+1) as u8, (i+2) as u32)));
        }
        let f = Cursor::new(vec![]);
        let mut cursor = TrieIOBuffer::new(f);
        let hash = TrieHash::from_data(&[0u8; 32]);
        let wres = Trie::write_nodetype(&mut cursor, &TrieNodeType::Node256(node256.clone()), hash.clone());
        assert!(wres.is_ok());

        fseek(&mut cursor, 0).unwrap();
        let root_ptr = cursor.root_ptr();
        let rres = Trie::read_node(&mut cursor, &TriePtr::new(TrieNodeID::Node256, 0, root_ptr as u32));
        
        assert!(rres.is_ok());
        assert_eq!(rres.unwrap(), (TrieNodeType::Node256(node256.clone()), hash));
    }
    
    #[test]
    fn read_write_leaf() {
        let leaf = TrieLeaf::new(
            &vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19], 
            &vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39]
        );

        let f = Cursor::new(vec![]);
        let mut cursor = TrieIOBuffer::new(f);
        let hash = TrieHash::from_data(&[0u8; 32]);
        let wres = Trie::write_nodetype(&mut cursor, &TrieNodeType::Leaf(leaf.clone()), hash.clone());
        assert!(wres.is_ok());

        fseek(&mut cursor, 0).unwrap();
        let rres = Trie::read_node(&mut cursor, &TriePtr::new(TrieNodeID::Leaf, 0, 0));
        
        assert!(rres.is_ok());
        assert_eq!(rres.unwrap(), (TrieNodeType::Leaf(leaf.clone()), hash));
    }

    #[test]
    fn read_write_node4_hashes() {
        let f = Cursor::new(vec![]);
        let mut cursor = TrieIOBuffer::new(f);
        let mut node4 = TrieNode4::new(&vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18]);
        let hash = TrieHash::from_data(&[0u8; 32]);

        let mut child_hashes = vec![];
        for i in 0..3 {
            let mut child = TrieLeaf::new(&vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,i as u8], &vec![i as u8; 40]);
            let mut child_hash = get_node_hash(&child, &vec![]);

            child_hashes.push(child_hash.clone());

            let ptr = ftell(&mut cursor).unwrap();
            Trie::write_node(&mut cursor, &child, child_hash).unwrap();
            assert!(node4.insert(&TriePtr::new(TrieNodeID::Leaf, i as u8, ptr as u32)));
        }

        // no final child
        child_hashes.push(TrieHash::from_data(&[]));
        
        let node4_ptr = ftell(&mut cursor).unwrap();
        let node4_hash = get_node_hash(&node4, &child_hashes);
        Trie::write_node(&mut cursor, &node4, node4_hash).unwrap();

        fseek(&mut cursor, node4_ptr).unwrap();
        let read_child_hashes = Trie::get_children_hashes(&mut cursor, &TrieNodeType::Node4(node4)).unwrap();

        assert_eq!(read_child_hashes, child_hashes);
    }

    #[test]
    fn read_write_node16_hashes() {
        let f = Cursor::new(vec![]);
        let mut cursor = TrieIOBuffer::new(f);
        let mut node16 = TrieNode16::new(&vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18]);
        let hash = TrieHash::from_data(&[0u8; 32]);

        let mut child_hashes = vec![];
        for i in 0..15 {
            let mut child = TrieLeaf::new(&vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,i as u8], &vec![i as u8; 40]);
            let mut child_hash = get_node_hash(&child, &vec![]);

            child_hashes.push(child_hash.clone());

            let ptr = ftell(&mut cursor).unwrap();
            Trie::write_node(&mut cursor, &child, child_hash).unwrap();
            assert!(node16.insert(&TriePtr::new(TrieNodeID::Leaf, i as u8, ptr as u32)));
        }

        // no final child
        child_hashes.push(TrieHash::from_data(&[]));
        
        let node16_ptr = ftell(&mut cursor).unwrap();
        let node16_hash = get_node_hash(&node16, &child_hashes);
        Trie::write_node(&mut cursor, &node16, node16_hash).unwrap();

        fseek(&mut cursor, node16_ptr).unwrap();
        let read_child_hashes = Trie::get_children_hashes(&mut cursor, &TrieNodeType::Node16(node16)).unwrap();

        assert_eq!(read_child_hashes, child_hashes);
    }

    #[test]
    fn read_write_node48_hashes() {
        let f = Cursor::new(vec![]);
        let mut cursor = TrieIOBuffer::new(f);
        let mut node48 = TrieNode48::new(&vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18]);
        let hash = TrieHash::from_data(&[0u8; 32]);

        let mut child_hashes = vec![];
        for i in 0..47 {
            let mut child = TrieLeaf::new(&vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,i as u8], &vec![i as u8; 40]);
            let mut child_hash = get_node_hash(&child, &vec![]);

            child_hashes.push(child_hash.clone());

            let ptr = ftell(&mut cursor).unwrap();
            Trie::write_node(&mut cursor, &child, child_hash).unwrap();
            assert!(node48.insert(&TriePtr::new(TrieNodeID::Leaf, i as u8, ptr as u32)));
        }

        // no final child
        child_hashes.push(TrieHash::from_data(&[]));
        
        let node48_ptr = ftell(&mut cursor).unwrap();
        let node48_hash = get_node_hash(&node48, &child_hashes);
        Trie::write_node(&mut cursor, &node48, node48_hash).unwrap();

        fseek(&mut cursor, node48_ptr).unwrap();
        let read_child_hashes = Trie::get_children_hashes(&mut cursor, &TrieNodeType::Node48(node48)).unwrap();

        assert_eq!(read_child_hashes, child_hashes);
    }

    #[test]
    fn read_write_node256_hashes() {
        let f = Cursor::new(vec![]);
        let mut cursor = TrieIOBuffer::new(f);

        let mut node256 = TrieNode256::new(&vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18]);
        let hash = TrieHash::from_data(&[0u8; 32]);

        let mut child_hashes = vec![];
        for i in 0..255 {
            let mut child = TrieLeaf::new(&vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,i as u8], &vec![i as u8; 40]);
            let mut child_hash = get_node_hash(&child, &vec![]);

            child_hashes.push(child_hash.clone());

            let ptr = ftell(&mut cursor).unwrap();
            Trie::write_node(&mut cursor, &child, child_hash).unwrap();
            assert!(node256.insert(&TriePtr::new(TrieNodeID::Leaf, i as u8, ptr as u32)));
        }

        // no final child
        child_hashes.push(TrieHash::from_data(&[]));
        
        let node256_ptr = ftell(&mut cursor).unwrap();
        let node256_hash = get_node_hash(&node256, &child_hashes);
        Trie::write_node(&mut cursor, &node256, node256_hash).unwrap();

        fseek(&mut cursor, node256_ptr).unwrap();
        let read_child_hashes = Trie::get_children_hashes(&mut cursor, &TrieNodeType::Node256(node256)).unwrap();

        assert_eq!(read_child_hashes, child_hashes);
    }

    fn make_node_path<S: TrieStorage + Seek>(s: &mut S, node_id: u8, path_segments: &Vec<(Vec<u8>, u8)>, leaf_data: Vec<u8>) -> (Vec<TrieNodeType>, Vec<TriePtr>, Vec<TrieHash>) {
        // make a fully-fleshed-out path of node's to a leaf 
        let root_ptr = s.root_ptr();
        fseek(s, root_ptr).unwrap();
        
        let root = TrieNode256::new(&path_segments[0].0);
        let root_hash = TrieHash::from_data(&[0u8; 32]);        // don't care about this in this test
        Trie::write_node(s, &root, root_hash.clone()).unwrap();

        let mut parent = TrieNodeType::Node256(root);
        let mut parent_ptr = 0;

        let mut nodes = vec![];
        let mut node_ptrs = vec![];
        let mut hashes = vec![];
        let mut seg_id = 0;

        for i in 0..path_segments.len() - 1 {
            let path_segment = &path_segments[i+1].0;
            let chr = path_segments[i].1;
            let node_ptr = ftell(s).unwrap();

            let node = match node_id {
                TrieNodeID::Node4 => TrieNodeType::Node4(TrieNode4::new(path_segment)),
                TrieNodeID::Node16 => TrieNodeType::Node16(TrieNode16::new(path_segment)),
                TrieNodeID::Node48 => TrieNodeType::Node48(TrieNode48::new(path_segment)),
                TrieNodeID::Node256 => TrieNodeType::Node256(TrieNode256::new(path_segment)),
                _ => panic!("invalid node ID")
            };

            Trie::write_nodetype(s, &node, TrieHash::from_data(&[(seg_id+1) as u8; 32])).unwrap();
            
            let sav = ftell(s).unwrap();

            // update parent 
            fseek(s, parent_ptr).unwrap();

            match parent {
                TrieNodeType::Node256(ref mut data) => assert!(data.insert(&TriePtr::new(node_id, chr, node_ptr as u32))),
                TrieNodeType::Node48(ref mut data) => assert!(data.insert(&TriePtr::new(node_id, chr, node_ptr as u32))),
                TrieNodeType::Node16(ref mut data) => assert!(data.insert(&TriePtr::new(node_id, chr, node_ptr as u32))),
                TrieNodeType::Node4(ref mut data) => assert!(data.insert(&TriePtr::new(node_id, chr, node_ptr as u32))),
                TrieNodeType::Leaf(ref mut data) => panic!("can't insert into leaf"),
            };

            Trie::write_nodetype(s, &parent, TrieHash::from_data(&[seg_id as u8; 32])).unwrap();
            
            fseek(s, sav).unwrap();
            
            nodes.push(parent.clone());
            node_ptrs.push(TriePtr::new(node_id, chr, node_ptr as u32));
            hashes.push(TrieHash::from_data(&[(seg_id+1) as u8; 32]));

            parent = node;
            parent_ptr = node_ptr;

            seg_id += 1;
        }

        // add a leaf at the end 
        let child = TrieLeaf::new(&path_segments[path_segments.len()-1].0, &leaf_data);
        let child_chr = path_segments[path_segments.len()-1].1;
        let child_ptr = ftell(s).unwrap();
        Trie::write_node(s, &child, TrieHash::from_data(&[(seg_id+1) as u8; 32])).unwrap();

        // update parent
        let sav = ftell(s).unwrap();
        fseek(s, parent_ptr).unwrap();

        match parent {
            TrieNodeType::Node256(ref mut data) => assert!(data.insert(&TriePtr::new(TrieNodeID::Leaf, child_chr, child_ptr as u32))),
            TrieNodeType::Node48(ref mut data) => assert!(data.insert(&TriePtr::new(TrieNodeID::Leaf, child_chr, child_ptr as u32))),
            TrieNodeType::Node16(ref mut data) => assert!(data.insert(&TriePtr::new(TrieNodeID::Leaf, child_chr, child_ptr as u32))),
            TrieNodeType::Node4(ref mut data) => assert!(data.insert(&TriePtr::new(TrieNodeID::Leaf, child_chr, child_ptr as u32))),
            TrieNodeType::Leaf(ref mut data) => panic!("can't insert into leaf"),
        };

        Trie::write_nodetype(s, &parent, TrieHash::from_data(&[(seg_id) as u8; 32])).unwrap();

        fseek(s, sav).unwrap();

        nodes.push(parent.clone());
        node_ptrs.push(TriePtr::new(TrieNodeID::Leaf, child_chr, child_ptr as u32));
        hashes.push(TrieHash::from_data(&[(seg_id+1) as u8; 32]));

        let root_ptr = s.root_ptr();
        fseek(s, root_ptr).unwrap();
        (nodes, node_ptrs, hashes)
    }
    
    fn make_node4_path<S: TrieStorage + Seek>(s: &mut S, path_segments: &Vec<(Vec<u8>, u8)>, leaf_data: Vec<u8>) -> (Vec<TrieNodeType>, Vec<TriePtr>, Vec<TrieHash>) {
        make_node_path(s, TrieNodeID::Node4, path_segments, leaf_data)
    }
    
    fn make_node16_path<S: TrieStorage + Seek>(s: &mut S, path_segments: &Vec<(Vec<u8>, u8)>, leaf_data: Vec<u8>) -> (Vec<TrieNodeType>, Vec<TriePtr>, Vec<TrieHash>) {
        make_node_path(s, TrieNodeID::Node16, path_segments, leaf_data)
    }
    
    fn make_node48_path<S: TrieStorage + Seek>(s: &mut S, path_segments: &Vec<(Vec<u8>, u8)>, leaf_data: Vec<u8>) -> (Vec<TrieNodeType>, Vec<TriePtr>, Vec<TrieHash>) {
        make_node_path(s, TrieNodeID::Node48, path_segments, leaf_data)
    }

    fn make_node256_path<S: TrieStorage + Seek>(s: &mut S, path_segments: &Vec<(Vec<u8>, u8)>, leaf_data: Vec<u8>) -> (Vec<TrieNodeType>, Vec<TriePtr>, Vec<TrieHash>) {
        make_node_path(s, TrieNodeID::Node256, path_segments, leaf_data)
    }

    #[test]
    fn trie_cursor_walk_full() {
        let cursor = Cursor::new(vec![]);
        let mut f = TrieIOBuffer::new(cursor);

        let path_segments = vec![
            (vec![], 0),
            (vec![], 1),
            (vec![], 2),
            (vec![], 3),
            (vec![], 4),
            (vec![], 5),
            (vec![], 6),
            (vec![], 7),
            (vec![], 8),
            (vec![], 9),
            (vec![], 10),
            (vec![], 11),
            (vec![], 12),
            (vec![], 13),
            (vec![], 14),
            (vec![], 15),
            (vec![], 16),
            (vec![], 17),
            (vec![], 18),
            (vec![], 19)
        ];
        let path = vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19];

        let (nodes, node_ptrs, hashes) = make_node4_path(&mut f, &path_segments, [19u8; 40].to_vec());

        assert_eq!(nodes.len(), 20);
        assert_eq!(node_ptrs.len(), 20);
        assert_eq!(hashes.len(), 20);

        assert_eq!(node_ptrs[node_ptrs.len()-1].chr, 19);
        assert_eq!(node_ptrs[node_ptrs.len()-1].id, TrieNodeID::Leaf);

        // walk down the trie
        fseek(&mut f, 0).unwrap();
        let mut c = TrieCursor::new(&TriePath::from_bytes(&path).unwrap(), f.root_ptr());
        let mut walk_point = nodes[0].clone();

        for i in 0..19 {
            let res = Trie::walk_from(&mut f, &walk_point, &mut c);
            assert!(res.is_ok());
            
            let fields_opt = res.unwrap();
            assert!(fields_opt.is_some());

            let (ptr, node, hash) = fields_opt.unwrap();
            assert_eq!(ptr, node_ptrs[i]);
            assert_eq!(hash, hashes[i]);
            assert_eq!(node, nodes[i+1]);

            assert_eq!(c.node().unwrap(), nodes[i]);
            assert_eq!(c.ptr(), node_ptrs[i]);
            assert_eq!(c.chr().unwrap(), path[i]);
            assert_eq!(c.tell(), i+1);
            assert_eq!(c.ntell(), 0);
            assert!(c.eonp(&c.node().unwrap()));

            walk_point = node;
        }

        // walk to the leaf
        let res = Trie::walk_from(&mut f, &walk_point, &mut c);
        assert!(res.is_ok());
        
        let fields_opt = res.unwrap();
        assert!(fields_opt.is_some());

        let (ptr, node, hash) = fields_opt.unwrap();
        assert_eq!(ptr, node_ptrs[19]);
        assert_eq!(node, TrieNodeType::Leaf(TrieLeaf::new(&vec![], &[19u8; 40].to_vec())));
        assert_eq!(hash, hashes[19]);

        // cursor's last-visited node points at the penultimate node (the last node4),
        // but its ptr() is the pointer to the leaf.
        assert_eq!(c.node().unwrap(), nodes[19]);
        assert_eq!(c.ptr(), node_ptrs[19]);
        assert_eq!(c.chr(), Some(path[path.len()-1]));
        assert_eq!(c.tell(), 20);
        assert!(c.eop());
        assert!(c.eonp(&c.node().unwrap()));

        dump_trie(&mut f);
    }
    
    #[test]
    fn trie_cursor_walk_1() {
        let cursor = Cursor::new(vec![]);
        let mut f = TrieIOBuffer::new(cursor);

        let path_segments = vec![
            (vec![0], 1),
            (vec![2], 3),
            (vec![4], 5),
            (vec![6], 7),
            (vec![8], 9),
            (vec![10], 11),
            (vec![12], 13),
            (vec![14], 15),
            (vec![16], 17),
            (vec![18], 19),
        ];
        let path = vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19];

        let (nodes, node_ptrs, hashes) = make_node4_path(&mut f, &path_segments, [19u8; 40].to_vec());

        assert_eq!(nodes.len(), 10);
        assert_eq!(node_ptrs.len(), 10);
        assert_eq!(hashes.len(), 10);

        assert_eq!(node_ptrs[node_ptrs.len()-1].chr, 19);
        assert_eq!(node_ptrs[node_ptrs.len()-1].id, TrieNodeID::Leaf);

        // walk down the trie
        fseek(&mut f, 0).unwrap();
        let mut c = TrieCursor::new(&TriePath::from_bytes(&path).unwrap(), f.root_ptr());
        let mut walk_point = nodes[0].clone();

        for i in 0..9 {
            let res = Trie::walk_from(&mut f, &walk_point, &mut c);
            assert!(res.is_ok());
            
            let fields_opt = res.unwrap();
            assert!(fields_opt.is_some());

            let (ptr, node, hash) = fields_opt.unwrap();
            assert_eq!(ptr, node_ptrs[i]);
            assert_eq!(hash, hashes[i]);
            assert_eq!(node, nodes[i+1]);

            assert_eq!(c.node().unwrap(), nodes[i]);
            assert_eq!(c.ptr(), node_ptrs[i]);
            assert_eq!(c.chr().unwrap(), path[2*(i+1)-1]);
            assert_eq!(c.tell(), 2*(i+1));
            assert_eq!(c.ntell(), 1);
            assert!(c.eonp(&c.node().unwrap()));

            walk_point = node;
        }

        // walk to the leaf
        let res = Trie::walk_from(&mut f, &walk_point, &mut c);
        assert!(res.is_ok());
        
        let fields_opt = res.unwrap();
        assert!(fields_opt.is_some());

        let (ptr, node, hash) = fields_opt.unwrap();
        assert_eq!(ptr, node_ptrs[9]);
        assert_eq!(node, TrieNodeType::Leaf(TrieLeaf::new(&vec![18], &[19u8; 40].to_vec())));
        assert_eq!(hash, hashes[9]);

        // cursor's last-visited node points at the penultimate node (the last node4),
        // but its ptr() is the pointer to the leaf.
        assert_eq!(c.node().unwrap(), nodes[9]);
        assert_eq!(c.ptr(), node_ptrs[9]);
        assert_eq!(c.chr(), Some(path[path.len()-1]));
        assert_eq!(c.tell(), 20);
        assert!(c.eop());
        assert!(c.eonp(&c.node().unwrap()));

        dump_trie(&mut f);
    }

    #[test]
    fn trie_cursor_walk_2() {
        let cursor = Cursor::new(vec![]);
        let mut f = TrieIOBuffer::new(cursor);

        let path_segments = vec![
            (vec![0,1], 2),
            (vec![3,4], 5),
            (vec![6,7], 8),
            (vec![9,10], 11),
            (vec![12,13], 14),
            (vec![15,16], 17),
            (vec![18], 19),
        ];
        let path = vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19];

        let (nodes, node_ptrs, hashes) = make_node4_path(&mut f, &path_segments, [19u8; 40].to_vec());

        assert_eq!(nodes.len(), 7);
        assert_eq!(node_ptrs.len(), 7);
        assert_eq!(hashes.len(), 7);

        assert_eq!(node_ptrs[node_ptrs.len()-1].chr, 19);
        assert_eq!(node_ptrs[node_ptrs.len()-1].id, TrieNodeID::Leaf);

        // walk down the trie
        fseek(&mut f, 0).unwrap();
        let mut c = TrieCursor::new(&TriePath::from_bytes(&path).unwrap(), f.root_ptr());
        let mut walk_point = nodes[0].clone();

        for i in 0..6 {
            let res = Trie::walk_from(&mut f, &walk_point, &mut c);
            assert!(res.is_ok());
            
            let fields_opt = res.unwrap();
            assert!(fields_opt.is_some());

            let (ptr, node, hash) = fields_opt.unwrap();
            assert_eq!(ptr, node_ptrs[i]);
            assert_eq!(hash, hashes[i]);
            assert_eq!(node, nodes[i+1]);

            assert_eq!(c.node().unwrap(), nodes[i]);
            assert_eq!(c.ptr(), node_ptrs[i]);
            assert_eq!(c.chr().unwrap(), path[3*(i+1)-1]);
            assert_eq!(c.tell(), 3*(i+1));
            assert_eq!(c.ntell(), 2);
            assert!(c.eonp(&c.node().unwrap()));

            walk_point = node;
        }

        // walk to the leaf
        let res = Trie::walk_from(&mut f, &walk_point, &mut c);
        assert!(res.is_ok());
        
        let fields_opt = res.unwrap();
        assert!(fields_opt.is_some());

        let (ptr, node, hash) = fields_opt.unwrap();
        assert_eq!(ptr, node_ptrs[6]);
        assert_eq!(node, TrieNodeType::Leaf(TrieLeaf::new(&vec![18], &[19u8; 40].to_vec())));
        assert_eq!(hash, hashes[6]);

        // cursor's last-visited node points at the penultimate node (the last node4),
        // but its ptr() is the pointer to the leaf.
        assert_eq!(c.node().unwrap(), nodes[6]);
        assert_eq!(c.ptr(), node_ptrs[6]);
        assert_eq!(c.chr(), Some(path[path.len()-1]));
        assert_eq!(c.tell(), 20);
        assert!(c.eop());
        assert!(c.eonp(&c.node().unwrap()));

        dump_trie(&mut f);
    }

    #[test]
    fn trie_cursor_walk_3() {
        let cursor = Cursor::new(vec![]);
        let mut f = TrieIOBuffer::new(cursor);

        let path_segments = vec![
            (vec![0,1,2], 3),
            (vec![4,5,6], 7),
            (vec![8,9,10], 11),
            (vec![12,13,14], 15),
            (vec![16,17,18], 19),
        ];
        let path = vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19];

        let (nodes, node_ptrs, hashes) = make_node4_path(&mut f, &path_segments, [19u8; 40].to_vec());

        assert_eq!(nodes.len(), 5);
        assert_eq!(node_ptrs.len(), 5);
        assert_eq!(hashes.len(), 5);

        assert_eq!(node_ptrs[node_ptrs.len()-1].chr, 19);
        assert_eq!(node_ptrs[node_ptrs.len()-1].id, TrieNodeID::Leaf);

        // walk down the trie
        fseek(&mut f, 0).unwrap();
        let mut c = TrieCursor::new(&TriePath::from_bytes(&path).unwrap(), f.root_ptr());
        let mut walk_point = nodes[0].clone();

        for i in 0..4 {
            let res = Trie::walk_from(&mut f, &walk_point, &mut c);
            assert!(res.is_ok());
            
            let fields_opt = res.unwrap();
            assert!(fields_opt.is_some());

            let (ptr, node, hash) = fields_opt.unwrap();
            assert_eq!(ptr, node_ptrs[i]);
            assert_eq!(hash, hashes[i]);
            assert_eq!(node, nodes[i+1]);

            assert_eq!(c.node().unwrap(), nodes[i]);
            assert_eq!(c.ptr(), node_ptrs[i]);
            assert_eq!(c.chr().unwrap(), path[4*(i+1)-1]);
            assert_eq!(c.tell(), 4*(i+1));
            assert_eq!(c.ntell(), 3);
            assert!(c.eonp(&c.node().unwrap()));

            walk_point = node;
        }

        // walk to the leaf
        let res = Trie::walk_from(&mut f, &walk_point, &mut c);
        assert!(res.is_ok());
        
        let fields_opt = res.unwrap();
        assert!(fields_opt.is_some());

        let (ptr, node, hash) = fields_opt.unwrap();
        assert_eq!(ptr, node_ptrs[4]);
        assert_eq!(node, TrieNodeType::Leaf(TrieLeaf::new(&vec![16,17,18], &[19u8; 40].to_vec())));
        assert_eq!(hash, hashes[4]);

        // cursor's last-visited node points at the penultimate node (the last node4),
        // but its ptr() is the pointer to the leaf.
        assert_eq!(c.node().unwrap(), nodes[4]);
        assert_eq!(c.ptr(), node_ptrs[4]);
        assert_eq!(c.chr(), Some(path[path.len()-1]));
        assert_eq!(c.tell(), 20);
        assert!(c.eop());
        assert!(c.eonp(&c.node().unwrap()));

        dump_trie(&mut f);
    }

    #[test]
    fn trie_cursor_walk_4() {
        let cursor = Cursor::new(vec![]);
        let mut f = TrieIOBuffer::new(cursor);

        let path_segments = vec![
            (vec![0,1,2,3], 4),
            (vec![5,6,7,8], 9),
            (vec![10,11,12,13], 14),
            (vec![15,16,17,18], 19)
        ];
        let path = vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19];

        let (nodes, node_ptrs, hashes) = make_node4_path(&mut f, &path_segments, [19u8; 40].to_vec());

        assert_eq!(nodes.len(), 4);
        assert_eq!(node_ptrs.len(), 4);
        assert_eq!(hashes.len(), 4);

        assert_eq!(node_ptrs[node_ptrs.len()-1].chr, 19);
        assert_eq!(node_ptrs[node_ptrs.len()-1].id, TrieNodeID::Leaf);

        // walk down the trie
        fseek(&mut f, 0).unwrap();
        let mut c = TrieCursor::new(&TriePath::from_bytes(&path).unwrap(), f.root_ptr());
        let mut walk_point = nodes[0].clone();

        for i in 0..3 {
            let res = Trie::walk_from(&mut f, &walk_point, &mut c);
            assert!(res.is_ok());
            
            let fields_opt = res.unwrap();
            assert!(fields_opt.is_some());
        
            let (ptr, node, hash) = fields_opt.unwrap();
            assert_eq!(ptr, node_ptrs[i]);
            assert_eq!(hash, hashes[i]);
            assert_eq!(node, nodes[i+1]);

            assert_eq!(c.node().unwrap(), nodes[i]);
            assert_eq!(c.ptr(), node_ptrs[i]);
            assert_eq!(c.chr().unwrap(), path[5*(i+1)-1]);
            assert_eq!(c.tell(), 5*(i+1));
            assert_eq!(c.ntell(), 4);
            assert!(c.eonp(&c.node().unwrap()));

            walk_point = node;
        }

        // walk to the leaf
        let res = Trie::walk_from(&mut f, &walk_point, &mut c);
        assert!(res.is_ok());
        
        let fields_opt = res.unwrap();
        assert!(fields_opt.is_some());

        let (ptr, node, hash) = fields_opt.unwrap();
        assert_eq!(ptr, node_ptrs[3]);
        assert_eq!(node, TrieNodeType::Leaf(TrieLeaf::new(&vec![15,16,17,18], &[19u8; 40].to_vec())));
        assert_eq!(hash, hashes[3]);

        // cursor's last-visited node points at the penultimate node (the last node4),
        // but its ptr() is the pointer to the leaf.
        assert_eq!(c.node().unwrap(), nodes[3]);
        assert_eq!(c.ptr(), node_ptrs[3]);
        assert_eq!(c.chr(), Some(path[path.len()-1]));
        assert_eq!(c.tell(), 20);
        assert!(c.eop());
        assert!(c.eonp(&c.node().unwrap()));

        dump_trie(&mut f);
    }

    #[test]
    fn trie_cursor_walk_5() {
        let cursor = Cursor::new(vec![]);
        let mut f = TrieIOBuffer::new(cursor);

        let path_segments = vec![
            (vec![0,1,2,3,4], 5),
            (vec![6,7,8,9,10], 11),
            (vec![12,13,14,15,16], 17),
            (vec![18], 19),
        ];
        let path = vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19];

        let (nodes, node_ptrs, hashes) = make_node4_path(&mut f, &path_segments, [19u8; 40].to_vec());

        assert_eq!(nodes.len(), 4);
        assert_eq!(node_ptrs.len(), 4);
        assert_eq!(hashes.len(), 4);

        assert_eq!(node_ptrs[node_ptrs.len()-1].chr, 19);
        assert_eq!(node_ptrs[node_ptrs.len()-1].id, TrieNodeID::Leaf);

        // walk down the trie
        fseek(&mut f, 0).unwrap();
        let mut c = TrieCursor::new(&TriePath::from_bytes(&path).unwrap(), f.root_ptr());
        let mut walk_point = nodes[0].clone();

        for i in 0..3 {
            let res = Trie::walk_from(&mut f, &walk_point, &mut c);
            assert!(res.is_ok());
            
            let fields_opt = res.unwrap();
            assert!(fields_opt.is_some());
        
            let (ptr, node, hash) = fields_opt.unwrap();
            assert_eq!(ptr, node_ptrs[i]);
            assert_eq!(hash, hashes[i]);
            assert_eq!(node, nodes[i+1]);

            assert_eq!(c.node().unwrap(), nodes[i]);
            assert_eq!(c.ptr(), node_ptrs[i]);
            assert_eq!(c.chr().unwrap(), path[6*(i+1)-1]);
            assert_eq!(c.tell(), 6*(i+1));
            assert_eq!(c.ntell(), 5);
            assert!(c.eonp(&c.node().unwrap()));

            walk_point = node;
        }

        // walk to the leaf
        let res = Trie::walk_from(&mut f, &walk_point, &mut c);
        assert!(res.is_ok());
        
        let fields_opt = res.unwrap();
        assert!(fields_opt.is_some());

        let (ptr, node, hash) = fields_opt.unwrap();
        assert_eq!(ptr, node_ptrs[3]);
        assert_eq!(node, TrieNodeType::Leaf(TrieLeaf::new(&vec![18], &[19u8; 40].to_vec())));
        assert_eq!(hash, hashes[3]);

        // cursor's last-visited node points at the penultimate node (the last node4),
        // but its ptr() is the pointer to the leaf.
        assert_eq!(c.node().unwrap(), nodes[3]);
        assert_eq!(c.ptr(), node_ptrs[3]);
        assert_eq!(c.chr(), Some(path[path.len()-1]));
        assert_eq!(c.tell(), 20);
        assert!(c.eop());
        assert!(c.eonp(&c.node().unwrap()));

        dump_trie(&mut f);
    }
    
    #[test]
    fn trie_cursor_walk_6() {
        let cursor = Cursor::new(vec![]);
        let mut f = TrieIOBuffer::new(cursor);

        let path_segments = vec![
            (vec![0,1,2,3,4,5], 6),
            (vec![7,8,9,10,11,12], 13),
            (vec![14,15,16,17,18], 19)
        ];
        let path = vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19];

        let (nodes, node_ptrs, hashes) = make_node4_path(&mut f, &path_segments, [19u8; 40].to_vec());

        assert_eq!(nodes.len(), 3);
        assert_eq!(node_ptrs.len(), 3);
        assert_eq!(hashes.len(), 3);

        assert_eq!(node_ptrs[node_ptrs.len()-1].chr, 19);
        assert_eq!(node_ptrs[node_ptrs.len()-1].id, TrieNodeID::Leaf);

        // walk down the trie
        fseek(&mut f, 0).unwrap();
        let mut c = TrieCursor::new(&TriePath::from_bytes(&path).unwrap(), f.root_ptr());
        let mut walk_point = nodes[0].clone();

        for i in 0..2 {
            let res = Trie::walk_from(&mut f, &walk_point, &mut c);
            assert!(res.is_ok());
            
            let fields_opt = res.unwrap();
            assert!(fields_opt.is_some());
        
            let (ptr, node, hash) = fields_opt.unwrap();
            assert_eq!(ptr, node_ptrs[i]);
            assert_eq!(hash, hashes[i]);
            assert_eq!(node, nodes[i+1]);

            assert_eq!(c.node().unwrap(), nodes[i]);
            assert_eq!(c.ptr(), node_ptrs[i]);
            assert_eq!(c.chr().unwrap(), path[7*(i+1)-1]);
            assert_eq!(c.tell(), 7*(i+1));
            assert_eq!(c.ntell(), 6);
            assert!(c.eonp(&c.node().unwrap()));

            walk_point = node;
        }

        // walk to the leaf
        let res = Trie::walk_from(&mut f, &walk_point, &mut c);
        assert!(res.is_ok());
        
        let fields_opt = res.unwrap();
        assert!(fields_opt.is_some());

        let (ptr, node, hash) = fields_opt.unwrap();
        assert_eq!(ptr, node_ptrs[2]);
        assert_eq!(node, TrieNodeType::Leaf(TrieLeaf::new(&vec![14,15,16,17,18], &[19u8; 40].to_vec())));
        assert_eq!(hash, hashes[2]);

        // cursor's last-visited node points at the penultimate node (the last node4),
        // but its ptr() is the pointer to the leaf.
        assert_eq!(c.node().unwrap(), nodes[2]);
        assert_eq!(c.ptr(), node_ptrs[2]);
        assert_eq!(c.chr(), Some(path[path.len()-1]));
        assert_eq!(c.tell(), 20);
        assert!(c.eop());
        assert!(c.eonp(&c.node().unwrap()));
        
        dump_trie(&mut f);
    }

    #[test]
    fn trie_cursor_walk_10() {
        let cursor = Cursor::new(vec![]);
        let mut f = TrieIOBuffer::new(cursor);

        let path_segments = vec![
            (vec![0,1,2,3,4,5,6,7,8,9], 10),
            (vec![11,12,13,14,15,16,17,18], 19)
        ];
        let path = vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19];

        let (nodes, node_ptrs, hashes) = make_node4_path(&mut f, &path_segments, [19u8; 40].to_vec());

        assert_eq!(nodes.len(), 2);
        assert_eq!(node_ptrs.len(), 2);
        assert_eq!(hashes.len(), 2);

        assert_eq!(node_ptrs[node_ptrs.len()-1].chr, 19);
        assert_eq!(node_ptrs[node_ptrs.len()-1].id, TrieNodeID::Leaf);

        // walk down the trie
        fseek(&mut f, 0).unwrap();
        let mut c = TrieCursor::new(&TriePath::from_bytes(&path).unwrap(), f.root_ptr());
        let mut walk_point = nodes[0].clone();

        for i in 0..1 {
            let res = Trie::walk_from(&mut f, &walk_point, &mut c);
            assert!(res.is_ok());
            
            let fields_opt = res.unwrap();
            assert!(fields_opt.is_some());
        
            let (ptr, node, hash) = fields_opt.unwrap();
            assert_eq!(ptr, node_ptrs[i]);
            assert_eq!(hash, hashes[i]);
            assert_eq!(node, nodes[i+1]);

            assert_eq!(c.node().unwrap(), nodes[i]);
            assert_eq!(c.ptr(), node_ptrs[i]);
            assert_eq!(c.chr().unwrap(), path[11*(i+1)-1]);
            assert_eq!(c.tell(), 11*(i+1));
            assert_eq!(c.ntell(), 10);
            assert!(c.eonp(&c.node().unwrap()));

            walk_point = node;
        }

        // walk to the leaf
        let res = Trie::walk_from(&mut f, &walk_point, &mut c);
        assert!(res.is_ok());
        
        let fields_opt = res.unwrap();
        assert!(fields_opt.is_some());

        let (ptr, node, hash) = fields_opt.unwrap();
        assert_eq!(ptr, node_ptrs[1]);
        assert_eq!(node, TrieNodeType::Leaf(TrieLeaf::new(&vec![11,12,13,14,15,16,17,18], &[19u8; 40].to_vec())));
        assert_eq!(hash, hashes[1]);

        // cursor's last-visited node points at the penultimate node (the last node4),
        // but its ptr() is the pointer to the leaf.
        assert_eq!(c.node().unwrap(), nodes[1]);
        assert_eq!(c.ptr(), node_ptrs[1]);
        assert_eq!(c.chr(), Some(path[path.len()-1]));
        assert_eq!(c.tell(), 20);
        assert!(c.eop());
        assert!(c.eonp(&c.node().unwrap()));
        
        dump_trie(&mut f);
    }

    #[test]
    fn trie_cursor_walk_20() {
        let cursor = Cursor::new(vec![]);
        let mut f = TrieIOBuffer::new(cursor);

        let path_segments = vec![
            (vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18], 19),
        ];
        let path = vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19];

        let (nodes, node_ptrs, hashes) = make_node4_path(&mut f, &path_segments, [19u8; 40].to_vec());

        assert_eq!(nodes.len(), 1);
        assert_eq!(node_ptrs.len(), 1);
        assert_eq!(hashes.len(), 1);

        assert_eq!(node_ptrs[node_ptrs.len()-1].chr, 19);
        assert_eq!(node_ptrs[node_ptrs.len()-1].id, TrieNodeID::Leaf);

        // walk down the trie
        fseek(&mut f, 0).unwrap();
        let mut c = TrieCursor::new(&TriePath::from_bytes(&path).unwrap(), f.root_ptr());
        let walk_point = nodes[0].clone();

        // walk to the leaf
        let res = Trie::walk_from(&mut f, &walk_point, &mut c);
        assert!(res.is_ok());
        
        let fields_opt = res.unwrap();
        assert!(fields_opt.is_some());

        let (ptr, node, hash) = fields_opt.unwrap();
        assert_eq!(ptr, node_ptrs[0]);
        assert_eq!(node, TrieNodeType::Leaf(TrieLeaf::new(&vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18], &[19u8; 40].to_vec())));
        assert_eq!(hash, hashes[0]);

        // cursor's last-visited node points at the penultimate node (the last node4),
        // but its ptr() is the pointer to the leaf.
        assert_eq!(c.node().unwrap(), nodes[0]);
        assert_eq!(c.ptr(), node_ptrs[0]);
        assert_eq!(c.chr(), Some(path[path.len()-1]));
        assert_eq!(c.tell(), 20);
        assert!(c.eop());
        assert!(c.eonp(&c.node().unwrap()));
        
        dump_trie(&mut f);
    }

    #[test]
    fn trie_cursor_try_attach_leaf() {
        for node_id in [TrieNodeID::Node4, TrieNodeID::Node16, TrieNodeID::Node48, TrieNodeID::Node256].iter() {
            let cursor = Cursor::new(vec![]);
            let mut f = TrieIOBuffer::new(cursor);

            let block_header = BlockHeaderHash::from_bytes(&[0u8; 32]).unwrap();
            MARF::format(&mut f, &block_header).unwrap();

            let path_segments = vec![
                (vec![], 0),
                (vec![], 1),
                (vec![], 2),
                (vec![], 3),
                (vec![], 4),
                (vec![], 5),
                (vec![], 6),
                (vec![], 7),
                (vec![], 8),
                (vec![], 9),
                (vec![], 10),
                (vec![], 11),
                (vec![], 12),
                (vec![], 13),
                (vec![], 14),
                (vec![], 15),
                (vec![], 16),
                (vec![], 17),
                (vec![], 18),
                (vec![], 19)
            ];
            let (nodes, node_ptrs, hashes) = make_node_path(&mut f, *node_id, &path_segments, [19u8; 40].to_vec());

            let mut ptrs = vec![];

            // append a leaf to each node
            for i in 0..20 {
                let mut path = vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19];
                path[i] = 20;

                let mut c = TrieCursor::new(&TriePath::from_bytes(&path[..]).unwrap(), f.root_ptr());
                let (mut node, root_hash) = Trie::read_root(&mut f).unwrap();
                for _ in 0..c.path.len() {
                    let next_opt = Trie::walk_from(&mut f, &node, &mut c).unwrap();
                    match next_opt {
                        Some((_next_node_ptr, next_node, _next_node_hash)) => {
                            // keep walking
                            node = next_node;
                            continue;
                        },
                        None => {
                            // end of path -- cursor points to the insertion point.
                            // all nodes have space, 
                            let ptr_opt_res = Trie::try_attach_leaf(&mut f, &c, &mut TrieLeaf::new(&vec![], &[i as u8; 40].to_vec()), &mut node);
                            assert!(ptr_opt_res.is_ok());

                            let ptr_opt = ptr_opt_res.unwrap();
                            assert!(ptr_opt.is_some());

                            let ptr = ptr_opt.unwrap();
                            ptrs.push(ptr.clone());
                        
                            let update_res = Trie::update_root_hash(&mut f, &c);
                            assert!(update_res.is_ok());

                            // we must be able to query it now 
                            let leaf_opt_res = MARF::get(&mut f, &block_header, &TriePath::from_bytes(&path[..]).unwrap());
                            assert!(leaf_opt_res.is_ok());
                            
                            let leaf_opt = leaf_opt_res.unwrap();
                            assert!(leaf_opt.is_some());

                            let leaf = leaf_opt.unwrap();
                            assert_eq!(leaf, TrieLeaf::new(&path[i+1..].to_vec(), &[i as u8; 40].to_vec()));

                            merkle_test(&mut f, &path, &[i as u8; 40].to_vec());
                            break;
                        }
                    }
                }
            }

            // look up each leaf we inserted
            for i in 0..20 {
                let mut path = vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19];
                path[i] = 20;

                let leaf_opt_res = MARF::get(&mut f, &block_header, &TriePath::from_bytes(&path[..]).unwrap());
                assert!(leaf_opt_res.is_ok());
                
                let leaf_opt = leaf_opt_res.unwrap();
                assert!(leaf_opt.is_some());

                let leaf = leaf_opt.unwrap();
                assert_eq!(leaf, TrieLeaf::new(&path[i+1..].to_vec(), &[i as u8; 40].to_vec()));
                
                merkle_test(&mut f, &path, &[i as u8; 40].to_vec());
            }

            // each ptr must be a node with two children
            for i in 0..20 {
                let ptr = &ptrs[i];
                let (node, hash) = Trie::read_node(&mut f, ptr).unwrap();
                match node {
                    TrieNodeType::Node4(ref data) => {
                        assert_eq!(count_children(&data.ptrs), 2)
                    },
                    TrieNodeType::Node16(ref data) => {
                        assert_eq!(count_children(&data.ptrs), 2)
                    },
                    TrieNodeType::Node48(ref data) => {
                        assert_eq!(count_children(&data.ptrs), 2)
                    },
                    TrieNodeType::Node256(ref data) => {
                        assert_eq!(count_children(&data.ptrs), 2)
                    },
                    _ => assert!(false)
                };
            }
            
            dump_trie(&mut f);
        }
    }

    #[test]
    fn trie_cursor_promote_leaf_to_node4() {
        let cursor = Cursor::new(vec![]);
        let mut f = TrieIOBuffer::new(cursor);

        let block_header = BlockHeaderHash::from_bytes(&[0u8; 32]).unwrap();
        MARF::format(&mut f, &block_header).unwrap();

        let (mut node, root_hash) = Trie::read_root(&mut f).unwrap();

        // add a single leaf
        let mut c = TrieCursor::new(&TriePath::from_bytes(&[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19]).unwrap(), f.root_ptr());

        for i in 0..c.path.len() {
            let next_opt = Trie::walk_from(&mut f, &node, &mut c).unwrap();
            match next_opt {
                Some((_next_node_ptr, next_node, _next_node_hash)) => {
                    // keep walking
                    node = next_node;
                    continue;
                },
                None => {
                    // end of path -- cursor points to the insertion point
                    Trie::try_attach_leaf(&mut f, &c, &mut TrieLeaf::new(&vec![], &[128; 40].to_vec()), &mut node).unwrap().unwrap();
                    Trie::update_root_hash(&mut f, &c).unwrap();

                    // should have taken one step
                    assert_eq!(i, 0);
                    break;
                }
            }
        }

        assert_eq!(MARF::get(&mut f, &block_header, &TriePath::from_bytes(&[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19]).unwrap()).unwrap().unwrap(), 
                   TrieLeaf::new(&vec![1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19], &[128; 40].to_vec()));

        merkle_test(&mut f, &[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19].to_vec(), &[128; 40].to_vec());

        let mut ptrs = vec![];

        // add more leaves -- unzip this path completely
        for j in 1..20 {
            // add a leaf that would go after the prior leaf
            let mut path = vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19];
            path[j] = 20;

            let mut c = TrieCursor::new(&TriePath::from_bytes(&path[..]).unwrap(), f.root_ptr());
            let (mut node, root_hash) = Trie::read_root(&mut f).unwrap();
            let mut node_ptr = TriePtr::new(0,0,0);

            for i in 0..c.path.len() {
                let next_opt = Trie::walk_from(&mut f, &node, &mut c).unwrap();
                match next_opt {
                    Some((next_node_ptr, next_node, _next_node_hash)) => {
                        // keep walking
                        node = next_node;
                        node_ptr = next_node_ptr;
                        continue;
                    },
                    None => {
                        // end of path -- cursor points to the insertion point
                        let mut leaf_data = match node {
                            TrieNodeType::Leaf(ref data) => data.clone(),
                            _ => panic!("not a leaf")
                        };

                        fseek(&mut f, node_ptr.ptr() as u64).unwrap();
                        let ptr = Trie::promote_leaf_to_node4(&mut f, &mut c, &mut leaf_data, &mut TrieLeaf::new(&vec![], &[(i + 128) as u8; 40].to_vec())).unwrap();
                        ptrs.push(ptr);

                        Trie::update_root_hash(&mut f, &c).unwrap();

                        // make sure we can query it again 
                        let leaf_opt_res = MARF::get(&mut f, &block_header, &TriePath::from_bytes(&path[..]).unwrap());
                        assert!(leaf_opt_res.is_ok());
                        
                        let leaf_opt = leaf_opt_res.unwrap();
                        assert!(leaf_opt.is_some());

                        let leaf = leaf_opt.unwrap();
                        assert_eq!(leaf, TrieLeaf::new(&path[i+1..].to_vec(), &[(i + 128) as u8; 40].to_vec()));
                        
                        merkle_test(&mut f, &path, &[(i + 128) as u8; 40].to_vec());
                        break;
                    }
                }
            }
        }

        // look up each leaf we inserted
        for i in 1..20 {
            let mut path = vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19];
            path[i] = 20;

            let leaf_opt_res = MARF::get(&mut f, &block_header, &TriePath::from_bytes(&path[..]).unwrap());
            assert!(leaf_opt_res.is_ok());
            
            let leaf_opt = leaf_opt_res.unwrap();
            assert!(leaf_opt.is_some());

            let leaf = leaf_opt.unwrap();
            assert_eq!(leaf, TrieLeaf::new(&path[i+1..].to_vec(), &[(i + 128) as u8; 40].to_vec()));
            
            merkle_test(&mut f, &path, &[(i + 128) as u8; 40].to_vec());
        }

        // each ptr must be a node with two children
        for i in 0..19 {
            let ptr = &ptrs[i];
            let (node, hash) = Trie::read_node(&mut f, ptr).unwrap();
            match node {
                TrieNodeType::Node4(ref data) => {
                    assert_eq!(count_children(&data.ptrs), 2)
                },
                TrieNodeType::Node256(ref data) => {
                    assert_eq!(count_children(&data.ptrs), 2)
                },
                _ => assert!(false)
            };
        }

        dump_trie(&mut f);
    }

    #[test]
    fn trie_cursor_promote_node4_to_node16() {
        let cursor = Cursor::new(vec![]);
        let mut f = TrieIOBuffer::new(cursor);
        
        let block_header = BlockHeaderHash::from_bytes(&[0u8; 32]).unwrap();
        MARF::format(&mut f, &block_header).unwrap();

        let path_segments = vec![
            (vec![], 0),
            (vec![], 1),
            (vec![], 2),
            (vec![], 3),
            (vec![], 4),
            (vec![], 5),
            (vec![], 6),
            (vec![], 7),
            (vec![], 8),
            (vec![], 9),
            (vec![], 10),
            (vec![], 11),
            (vec![], 12),
            (vec![], 13),
            (vec![], 14),
            (vec![], 15),
            (vec![], 16),
            (vec![], 17),
            (vec![], 18),
            (vec![], 19)
        ];
        let (nodes, node_ptrs, hashes) = make_node4_path(&mut f, &path_segments, [19u8; 40].to_vec());

        let (node, root_hash) = Trie::read_root(&mut f).unwrap();

        // fill each node4
        for k in 0..19 {
            for j in 0..3 {
                let mut path = [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19];
                path[k] = j + 20;

                let mut c = TrieCursor::new(&TriePath::from_bytes(&path[..]).unwrap(), f.root_ptr());
                let (mut node, hash) = Trie::read_root(&mut f).unwrap();

                for i in 0..c.path.len() {
                    let next_opt = Trie::walk_from(&mut f, &node, &mut c).unwrap();
                    match next_opt {
                        Some((_next_node_ptr, next_node, _next_node_hash)) => {
                            // keep walking
                            node = next_node;
                            continue;
                        },
                        None => {
                            // end of path -- cursor points to the insertion point
                            Trie::try_attach_leaf(&mut f, &c, &mut TrieLeaf::new(&vec![], &[128 + j as u8; 40].to_vec()), &mut node).unwrap().unwrap();
                            Trie::update_root_hash(&mut f, &c).unwrap();
                            break;
                        }
                    }
                }

                // should have inserted
                assert_eq!(MARF::get(&mut f, &block_header, &TriePath::from_bytes(&path[..]).unwrap()).unwrap().unwrap(),
                           TrieLeaf::new(&path[k+1..].to_vec(), &[128 + j as u8; 40].to_vec()));
            
                merkle_test(&mut f, &path.to_vec(), &[(j + 128) as u8; 40].to_vec());
            }
        }

        test_debug!("");
        test_debug!("");
        test_debug!("");
            
        let mut ptrs = vec![];

        // promote each node4 to a node16 
        for k in 1..19 {
            let mut path = [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19];
            path[k] = 128;

            let mut c = TrieCursor::new(&TriePath::from_bytes(&path[..]).unwrap(), f.root_ptr());
            let (mut node, hash) = Trie::read_root(&mut f).unwrap();

            for i in 0..c.path.len() {
                let next_opt = Trie::walk_from(&mut f, &node, &mut c).unwrap();
                match next_opt {
                    Some((_next_node_ptr, next_node, _next_node_hash)) => {
                        // keep walking
                        node = next_node;
                        continue;
                    },
                    None => {
                        // end of path -- cursor points to the insertion point
                        let new_ptr = Trie::insert_leaf(&mut f, &mut c, &mut TrieLeaf::new(&vec![], &[192 + k as u8; 40].to_vec()), &mut node).unwrap();
                        ptrs.push(new_ptr);

                        Trie::update_root_hash(&mut f, &c).unwrap();
                        break;
                    }
                }
            }

            // should have inserted
            assert_eq!(MARF::get(&mut f, &block_header, &TriePath::from_bytes(&path[..]).unwrap()).unwrap().unwrap(),
                       TrieLeaf::new(&path[k+1..].to_vec(), &[192 + k as u8; 40].to_vec()));
            
            merkle_test(&mut f, &path.to_vec(), &[(k + 192) as u8; 40].to_vec());
        }

        // each ptr we got should point to a node16 with 5 children
        for ptr in ptrs.iter() {
            let (node, hash) = Trie::read_node(&mut f, ptr).unwrap();
            match node {
                TrieNodeType::Node16(ref data) => {
                    assert_eq!(count_children(&data.ptrs), 5);
                },
                _ => {
                    assert!(false);
                }
            }
        }

        dump_trie(&mut f);
    }

    #[test]
    fn trie_cursor_promote_node16_to_node48() {
        let cursor = Cursor::new(vec![]);
        let mut f = TrieIOBuffer::new(cursor);
        
        let block_header = BlockHeaderHash::from_bytes(&[0u8; 32]).unwrap();
        MARF::format(&mut f, &block_header).unwrap();

        let path_segments = vec![
            (vec![], 0),
            (vec![], 1),
            (vec![], 2),
            (vec![], 3),
            (vec![], 4),
            (vec![], 5),
            (vec![], 6),
            (vec![], 7),
            (vec![], 8),
            (vec![], 9),
            (vec![], 10),
            (vec![], 11),
            (vec![], 12),
            (vec![], 13),
            (vec![], 14),
            (vec![], 15),
            (vec![], 16),
            (vec![], 17),
            (vec![], 18),
            (vec![], 19)
        ];
        let (nodes, node_ptrs, hashes) = make_node4_path(&mut f, &path_segments, [19u8; 40].to_vec());

        let (node, root_hash) = Trie::read_root(&mut f).unwrap();

        // fill each node4
        for k in 0..19 {
            for j in 0..3 {
                let mut path = [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19];
                path[k] = j + 20;

                let mut c = TrieCursor::new(&TriePath::from_bytes(&path[..]).unwrap(), f.root_ptr());
                let (mut node, hash) = Trie::read_root(&mut f).unwrap();

                for i in 0..c.path.len() {
                    let next_opt = Trie::walk_from(&mut f, &node, &mut c).unwrap();
                    match next_opt {
                        Some((_next_node_ptr, next_node, _next_node_hash)) => {
                            // keep walking
                            node = next_node;
                            continue;
                        },
                        None => {
                            // end of path -- cursor points to the insertion point
                            Trie::try_attach_leaf(&mut f, &c, &mut TrieLeaf::new(&vec![], &[128 + j as u8; 40].to_vec()), &mut node).unwrap().unwrap();
                            Trie::update_root_hash(&mut f, &c).unwrap();
                            break;
                        }
                    }
                }

                // should have inserted
                assert_eq!(MARF::get(&mut f, &block_header, &TriePath::from_bytes(&path[..]).unwrap()).unwrap().unwrap(),
                           TrieLeaf::new(&path[k+1..].to_vec(), &[128 + j as u8; 40].to_vec()));
                
                merkle_test(&mut f, &path.to_vec(), &[(j + 128) as u8; 40].to_vec());
            }
        }

        test_debug!("");
        test_debug!("promote all node4 to node16");
        test_debug!("");
            
        let mut ptrs = vec![];

        // promote each node4 to a node16 by inserting one more leaf 
        for k in 1..19 {
            let mut path = [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19];
            path[k] = 128;

            let mut c = TrieCursor::new(&TriePath::from_bytes(&path[..]).unwrap(), f.root_ptr());
            let (mut node, hash) = Trie::read_root(&mut f).unwrap();

            for i in 0..c.path.len() {
                let next_opt = Trie::walk_from(&mut f, &node, &mut c).unwrap();
                match next_opt {
                    Some((_next_node_ptr, next_node, _next_node_hash)) => {
                        // keep walking
                        node = next_node;
                        continue;
                    },
                    None => {
                        // end of path -- cursor points to the insertion point
                        let new_ptr = Trie::insert_leaf(&mut f, &mut c, &mut TrieLeaf::new(&vec![], &[192 + k as u8; 40].to_vec()), &mut node).unwrap();
                        ptrs.push(new_ptr);

                        Trie::update_root_hash(&mut f, &c).unwrap();
                        break;
                    }
                }
            }

            // should have inserted
            assert_eq!(MARF::get(&mut f, &block_header, &TriePath::from_bytes(&path[..]).unwrap()).unwrap().unwrap(),
                       TrieLeaf::new(&path[k+1..].to_vec(), &[192 + k as u8; 40].to_vec()));
            
            merkle_test(&mut f, &path.to_vec(), &[(k + 192) as u8; 40].to_vec());
        }

        // each ptr we got should point to a node16 with 5 children
        for ptr in ptrs.iter() {
            let (node, hash) = Trie::read_node(&mut f, ptr).unwrap();
            match node {
                TrieNodeType::Node16(ref data) => {
                    assert_eq!(count_children(&data.ptrs), 5);
                },
                _ => {
                    assert!(false);
                }
            }
        }

        // fill each node16 with leaves
        for k in 0..19 {
            for j in 0..11 {
                let mut path = [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19];
                path[k] = j + 40;

                let mut c = TrieCursor::new(&TriePath::from_bytes(&path[..]).unwrap(), f.root_ptr());
                let (mut node, hash) = Trie::read_root(&mut f).unwrap();

                for i in 0..c.path.len() {
                    let next_opt = Trie::walk_from(&mut f, &node, &mut c).unwrap();
                    match next_opt {
                        Some((_next_node_ptr, next_node, _next_node_hash)) => {
                            // keep walking
                            node = next_node;
                            continue;
                        },
                        None => {
                            // end of path -- cursor points to the insertion point
                            Trie::try_attach_leaf(&mut f, &c, &mut TrieLeaf::new(&vec![], &[128 + j as u8; 40].to_vec()), &mut node).unwrap().unwrap();
                            Trie::update_root_hash(&mut f, &c).unwrap();
                            break;
                        }
                    }
                }

                // should have inserted
                assert_eq!(MARF::get(&mut f, &block_header, &TriePath::from_bytes(&path[..]).unwrap()).unwrap().unwrap(),
                           TrieLeaf::new(&path[k+1..].to_vec(), &[128 + j as u8; 40].to_vec()));

                merkle_test(&mut f, &path.to_vec(), &[(j + 128) as u8; 40].to_vec());
            }
        }

        test_debug!("");
        test_debug!("promote all node16 to node48");
        test_debug!("");
            
        ptrs.clear();

        // promote each node16 to a node48 by inserting one more leaf
        for k in 1..19 {
            let mut path = [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19];
            path[k] = 129;

            let mut c = TrieCursor::new(&TriePath::from_bytes(&path[..]).unwrap(), f.root_ptr());
            let (mut node, hash) = Trie::read_root(&mut f).unwrap();

            test_debug!("Start insert at {:?}", &c);
            for i in 0..c.path.len() {
                let next_opt = Trie::walk_from(&mut f, &node, &mut c).unwrap();
                match next_opt {
                    Some((_next_node_ptr, next_node, _next_node_hash)) => {
                        // keep walking
                        node = next_node;
                        continue;
                    },
                    None => {
                        // end of path -- cursor points to the insertion point
                        test_debug!("Insert leaf pattern={} at {:?}", 192 + k, &c);
                        let new_ptr = Trie::insert_leaf(&mut f, &mut c, &mut TrieLeaf::new(&vec![], &[192 + k as u8; 40].to_vec()), &mut node).unwrap();
                        ptrs.push(new_ptr);

                        Trie::update_root_hash(&mut f, &c).unwrap();
                        break;
                    }
                }
            }

            // should have inserted
            assert_eq!(MARF::get(&mut f, &block_header, &TriePath::from_bytes(&path[..]).unwrap()).unwrap().unwrap(),
                       TrieLeaf::new(&path[k+1..].to_vec(), &[192 + k as u8; 40].to_vec()));

            merkle_test(&mut f, &path.to_vec(), &[(k + 192) as u8; 40].to_vec());
        }

        // each ptr we got should point to a node48 with 17 children
        for ptr in ptrs.iter() {
            let (node, hash) = Trie::read_node(&mut f, ptr).unwrap();
            match node {
                TrieNodeType::Node48(ref data) => {
                    assert_eq!(count_children(&data.ptrs), 17);
                },
                _ => {
                    assert!(false);
                }
            }
        }

        dump_trie(&mut f);
    }

    #[test]
    fn trie_cursor_promote_node48_to_node256() {
        let cursor = Cursor::new(vec![]);
        let mut f = TrieIOBuffer::new(cursor);
        
        let block_header = BlockHeaderHash::from_bytes(&[0u8; 32]).unwrap();
        MARF::format(&mut f, &block_header).unwrap();

        let path_segments = vec![
            (vec![], 0),
            (vec![], 1),
            (vec![], 2),
            (vec![], 3),
            (vec![], 4),
            (vec![], 5),
            (vec![], 6),
            (vec![], 7),
            (vec![], 8),
            (vec![], 9),
            (vec![], 10),
            (vec![], 11),
            (vec![], 12),
            (vec![], 13),
            (vec![], 14),
            (vec![], 15),
            (vec![], 16),
            (vec![], 17),
            (vec![], 18),
            (vec![], 19)
        ];
        let (nodes, node_ptrs, hashes) = make_node4_path(&mut f, &path_segments, [19u8; 40].to_vec());

        let (node, root_hash) = Trie::read_root(&mut f).unwrap();

        // fill each node4
        for k in 0..19 {
            for j in 0..3 {
                let mut path = [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19];
                path[k] = j + 20;

                let mut c = TrieCursor::new(&TriePath::from_bytes(&path[..]).unwrap(), f.root_ptr());
                let (mut node, hash) = Trie::read_root(&mut f).unwrap();

                for i in 0..c.path.len() {
                    let next_opt = Trie::walk_from(&mut f, &node, &mut c).unwrap();
                    match next_opt {
                        Some((_next_node_ptr, next_node, _next_node_hash)) => {
                            // keep walking
                            node = next_node;
                            continue;
                        },
                        None => {
                            // end of path -- cursor points to the insertion point
                            Trie::try_attach_leaf(&mut f, &c, &mut TrieLeaf::new(&vec![], &[128 + j as u8; 40].to_vec()), &mut node).unwrap().unwrap();
                            Trie::update_root_hash(&mut f, &c).unwrap();
                            break;
                        }
                    }
                }

                // should have inserted
                assert_eq!(MARF::get(&mut f, &block_header, &TriePath::from_bytes(&path[..]).unwrap()).unwrap().unwrap(),
                           TrieLeaf::new(&path[k+1..].to_vec(), &[128 + j as u8; 40].to_vec()));
                
                merkle_test(&mut f, &path.to_vec(), &[(j + 128) as u8; 40].to_vec());
            }
        }

        test_debug!("");
        test_debug!("promote all node4 to node16");
        test_debug!("");
            
        let mut ptrs = vec![];

        // promote each node4 to a node16 by inserting one more leaf 
        for k in 1..19 {
            let mut path = [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19];
            path[k] = 128;

            let mut c = TrieCursor::new(&TriePath::from_bytes(&path[..]).unwrap(), f.root_ptr());
            let (mut node, hash) = Trie::read_root(&mut f).unwrap();

            for i in 0..c.path.len() {
                let next_opt = Trie::walk_from(&mut f, &node, &mut c).unwrap();
                match next_opt {
                    Some((_next_node_ptr, next_node, _next_node_hash)) => {
                        // keep walking
                        node = next_node;
                        continue;
                    },
                    None => {
                        // end of path -- cursor points to the insertion point
                        let new_ptr = Trie::insert_leaf(&mut f, &mut c, &mut TrieLeaf::new(&vec![], &[192 + k as u8; 40].to_vec()), &mut node).unwrap();
                        ptrs.push(new_ptr);

                        Trie::update_root_hash(&mut f, &c).unwrap();
                        break;
                    }
                }
            }

            // should have inserted
            assert_eq!(MARF::get(&mut f, &block_header, &TriePath::from_bytes(&path[..]).unwrap()).unwrap().unwrap(),
                       TrieLeaf::new(&path[k+1..].to_vec(), &[192 + k as u8; 40].to_vec()));

            merkle_test(&mut f, &path.to_vec(), &[(k + 192) as u8; 40].to_vec());
        }

        // each ptr we got should point to a node16 with 5 children
        for ptr in ptrs.iter() {
            let (node, hash) = Trie::read_node(&mut f, ptr).unwrap();
            match node {
                TrieNodeType::Node16(ref data) => {
                    assert_eq!(count_children(&data.ptrs), 5);
                },
                _ => {
                    assert!(false);
                }
            }
        }

        // fill each node16 with leaves
        for k in 0..19 {
            for j in 0..11 {
                let mut path = [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19];
                path[k] = j + 40;

                let mut c = TrieCursor::new(&TriePath::from_bytes(&path[..]).unwrap(), f.root_ptr());
                let (mut node, hash) = Trie::read_root(&mut f).unwrap();

                for i in 0..c.path.len() {
                    let next_opt = Trie::walk_from(&mut f, &node, &mut c).unwrap();
                    match next_opt {
                        Some((_next_node_ptr, next_node, _next_node_hash)) => {
                            // keep walking
                            node = next_node;
                            continue;
                        },
                        None => {
                            // end of path -- cursor points to the insertion point
                            Trie::try_attach_leaf(&mut f, &c, &mut TrieLeaf::new(&vec![], &[128 + j as u8; 40].to_vec()), &mut node).unwrap().unwrap();
                            Trie::update_root_hash(&mut f, &c).unwrap();
                            break;
                        }
                    }
                }

                // should have inserted
                assert_eq!(MARF::get(&mut f, &block_header, &TriePath::from_bytes(&path[..]).unwrap()).unwrap().unwrap(),
                           TrieLeaf::new(&path[k+1..].to_vec(), &[128 + j as u8; 40].to_vec()));
                
                merkle_test(&mut f, &path.to_vec(), &[(j + 128) as u8; 40].to_vec());
            }
        }

        test_debug!("");
        test_debug!("promote all node16 to node48");
        test_debug!("");
            
        ptrs.clear();

        // promote each node16 to a node48 by inserting one more leaf
        for k in 1..19 {
            let mut path = [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19];
            path[k] = 129;

            let mut c = TrieCursor::new(&TriePath::from_bytes(&path[..]).unwrap(), f.root_ptr());
            let (mut node, hash) = Trie::read_root(&mut f).unwrap();

            test_debug!("Start insert at {:?}", &c);
            for i in 0..c.path.len() {
                let next_opt = Trie::walk_from(&mut f, &node, &mut c).unwrap();
                match next_opt {
                    Some((_next_node_ptr, next_node, _next_node_hash)) => {
                        // keep walking
                        node = next_node;
                        continue;
                    },
                    None => {
                        // end of path -- cursor points to the insertion point
                        test_debug!("Insert leaf pattern={} at {:?}", 192 + k, &c);
                        let new_ptr = Trie::insert_leaf(&mut f, &mut c, &mut TrieLeaf::new(&vec![], &[192 + k as u8; 40].to_vec()), &mut node).unwrap();
                        ptrs.push(new_ptr);

                        Trie::update_root_hash(&mut f, &c).unwrap();
                        break;
                    }
                }
            }

            // should have inserted
            assert_eq!(MARF::get(&mut f, &block_header, &TriePath::from_bytes(&path[..]).unwrap()).unwrap().unwrap(),
                       TrieLeaf::new(&path[k+1..].to_vec(), &[192 + k as u8; 40].to_vec()));

            merkle_test(&mut f, &path.to_vec(), &[(k + 192) as u8; 40].to_vec());
        }

        // each ptr we got should point to a node48 with 17 children
        for ptr in ptrs.iter() {
            let (node, hash) = Trie::read_node(&mut f, ptr).unwrap();
            match node {
                TrieNodeType::Node48(ref data) => {
                    assert_eq!(count_children(&data.ptrs), 17);
                },
                _ => {
                    assert!(false);
                }
            }
        }

        // fill each node48 with leaves
        for k in 0..19 {
            for j in 0..31 {
                let mut path = [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19];
                path[k] = j + 90;

                let mut c = TrieCursor::new(&TriePath::from_bytes(&path[..]).unwrap(), f.root_ptr());
                let (mut node, hash) = Trie::read_root(&mut f).unwrap();

                for i in 0..c.path.len() {
                    let next_opt = Trie::walk_from(&mut f, &node, &mut c).unwrap();
                    match next_opt {
                        Some((_next_node_ptr, next_node, _next_node_hash)) => {
                            // keep walking
                            node = next_node;
                            continue;
                        },
                        None => {
                            // end of path -- cursor points to the insertion point
                            Trie::try_attach_leaf(&mut f, &c, &mut TrieLeaf::new(&vec![], &[128 + j as u8; 40].to_vec()), &mut node).unwrap().unwrap();
                            Trie::update_root_hash(&mut f, &c).unwrap();
                            break;
                        }
                    }
                }

                // should have inserted
                assert_eq!(MARF::get(&mut f, &block_header, &TriePath::from_bytes(&path[..]).unwrap()).unwrap().unwrap(),
                           TrieLeaf::new(&path[k+1..].to_vec(), &[128 + j as u8; 40].to_vec()));
                
                merkle_test(&mut f, &path.to_vec(), &[(j + 128) as u8; 40].to_vec());
            }
        }
        
        test_debug!("");
        test_debug!("promote all node48 to node256");
        test_debug!("");
            
        ptrs.clear();

        // promote each node48 to a node256 by inserting one more leaf
        for k in 1..19 {
            let mut path = [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19];
            path[k] = 130;

            let mut c = TrieCursor::new(&TriePath::from_bytes(&path[..]).unwrap(), f.root_ptr());
            let (mut node, hash) = Trie::read_root(&mut f).unwrap();

            test_debug!("Start insert at {:?}", &c);
            for i in 0..c.path.len() {
                let next_opt = Trie::walk_from(&mut f, &node, &mut c).unwrap();
                match next_opt {
                    Some((_next_node_ptr, next_node, _next_node_hash)) => {
                        // keep walking
                        node = next_node;
                        continue;
                    },
                    None => {
                        // end of path -- cursor points to the insertion point
                        test_debug!("Insert leaf pattern={} at {:?}", 192 + k, &c);
                        let new_ptr = Trie::insert_leaf(&mut f, &mut c, &mut TrieLeaf::new(&vec![], &[192 + k as u8; 40].to_vec()), &mut node).unwrap();
                        ptrs.push(new_ptr);

                        Trie::update_root_hash(&mut f, &c).unwrap();
                        break;
                    }
                }
            }

            // should have inserted
            assert_eq!(MARF::get(&mut f, &block_header, &TriePath::from_bytes(&path[..]).unwrap()).unwrap().unwrap(),
                       TrieLeaf::new(&path[k+1..].to_vec(), &[192 + k as u8; 40].to_vec()));
            
            merkle_test(&mut f, &path.to_vec(), &[(k + 192) as u8; 40].to_vec());
        }

        // each ptr we got should point to a node256 with 49 children
        for ptr in ptrs.iter() {
            let (node, hash) = Trie::read_node(&mut f, ptr).unwrap();
            match node {
                TrieNodeType::Node256(ref data) => {
                    assert_eq!(count_children(&data.ptrs), 49);
                },
                _ => {
                    assert!(false);
                }
            }
        }

        dump_trie(&mut f);
    }

    #[test]
    fn trie_cursor_splice_leaf_4() {
        for node_id in [TrieNodeID::Node4, TrieNodeID::Node16, TrieNodeID::Node48, TrieNodeID::Node256].iter() {
            let cursor = Cursor::new(vec![]);
            let mut f = TrieIOBuffer::new(cursor);

            let block_header = BlockHeaderHash::from_bytes(&[0u8; 32]).unwrap();
            MARF::format(&mut f, &block_header).unwrap();

            let path_segments = vec![
                (vec![0,1,2,3], 4),
                (vec![5,6,7,8], 9),
                (vec![10,11,12,13], 14),
                (vec![15,16,17,18], 19)
            ];

            let (nodes, node_ptrs, hashes) = make_node_path(&mut f, *node_id, &path_segments, [19u8; 40].to_vec());
            let mut ptrs = vec![];

            // splice in a node in each path segment 
            for k in 0..3 {
                let mut path = vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19];
                path[4*k + 2] = 20;

                let mut c = TrieCursor::new(&TriePath::from_bytes(&path[..]).unwrap(), f.root_ptr());
                let (mut node, hash) = Trie::read_root(&mut f).unwrap();

                test_debug!("Start splice-insert at {:?}", &c);
                for i in 0..c.path.len() {
                    let next_opt = Trie::walk_from(&mut f, &node, &mut c).unwrap();
                    match next_opt {
                        Some((_next_node_ptr, next_node, _next_node_hash)) => {
                            // keep walking
                            node = next_node;
                            continue;
                        },
                        None => {
                            // end of path -- cursor points to the insertion point
                            test_debug!("Splice leaf pattern={} at {:?}", 192 + k, &c);
                            let new_ptr = Trie::splice_leaf(&mut f, &mut c, &mut TrieLeaf::new(&vec![], &[192 + k as u8; 40].to_vec()), &mut node).unwrap();
                            ptrs.push(new_ptr);

                            Trie::update_root_hash(&mut f, &c).unwrap();
                            break;
                        }
                    }
                }

                // should have inserted
                assert_eq!(MARF::get(&mut f, &block_header, &TriePath::from_bytes(&path[..]).unwrap()).unwrap().unwrap(),
                           TrieLeaf::new(&path[4*k+3..].to_vec(), &[192 + k as u8; 40].to_vec()));
                
                merkle_test(&mut f, &path.to_vec(), &[(k + 192) as u8; 40].to_vec());
            }

            dump_trie(&mut f);
        }
    }
    
    #[test]
    fn trie_cursor_splice_leaf_2() {
        for node_id in [TrieNodeID::Node4, TrieNodeID::Node16, TrieNodeID::Node48, TrieNodeID::Node256].iter() {
            let cursor = Cursor::new(vec![]);
            let mut f = TrieIOBuffer::new(cursor);
        
            let block_header = BlockHeaderHash::from_bytes(&[0u8; 32]).unwrap();
            MARF::format(&mut f, &block_header).unwrap();

            let path_segments = vec![
                (vec![0,1], 2),
                (vec![3,4], 5),
                (vec![6,7], 8),
                (vec![9,10], 11),
                (vec![12,13], 14),
                (vec![15,16], 17),
                (vec![18], 19)
            ];

            let (nodes, node_ptrs, hashes) = make_node_path(&mut f, *node_id, &path_segments, [19u8; 40].to_vec());
            let mut ptrs = vec![];

            // splice in a node in each path segment 
            for k in 0..6 {
                let mut path = vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19];
                path[3*k + 1] = 20;

                let mut c = TrieCursor::new(&TriePath::from_bytes(&path[..]).unwrap(), f.root_ptr());
                let (mut node, hash) = Trie::read_root(&mut f).unwrap();

                test_debug!("Start splice-insert at {:?}", &c);
                for i in 0..c.path.len() {
                    let next_opt = Trie::walk_from(&mut f, &node, &mut c).unwrap();
                    match next_opt {
                        Some((_next_node_ptr, next_node, _next_node_hash)) => {
                            // keep walking
                            node = next_node;
                            continue;
                        },
                        None => {
                            // end of path -- cursor points to the insertion point
                            test_debug!("Splice leaf pattern={} at {:?}", 192 + k, &c);
                            let new_ptr = Trie::splice_leaf(&mut f, &mut c, &mut TrieLeaf::new(&vec![], &[192 + k as u8; 40].to_vec()), &mut node).unwrap();
                            ptrs.push(new_ptr);

                            Trie::update_root_hash(&mut f, &c).unwrap();
                            break;
                        }
                    }
                }

                // should have inserted
                assert_eq!(MARF::get(&mut f, &block_header, &TriePath::from_bytes(&path[..]).unwrap()).unwrap().unwrap(),
                           TrieLeaf::new(&path[3*k+2..].to_vec(), &[192 + k as u8; 40].to_vec()));
            }

            dump_trie(&mut f);
        }
    }

    #[test]
    fn insert_1024_seq_low() {
        let cursor = Cursor::new(vec![]);
        let mut f = TrieIOBuffer::new(cursor);

        let block_header = BlockHeaderHash::from_bytes(&[0u8; 32]).unwrap();
        MARF::format(&mut f, &block_header).unwrap();

        for i in 0..1024 {
            let i0 = i / 256;
            let i1 = i % 256;
            let path = [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,i0 as u8, i1 as u8];
            let triepath = TriePath::from_bytes(&path[..]).unwrap();
            let value = TrieLeaf::new(&vec![], &[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,i0 as u8, i1 as u8].to_vec());
            MARF::insert(&mut f, &block_header, &triepath, &value).unwrap();

            merkle_test(&mut f, &path.to_vec(), &[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,i0 as u8, i1 as u8].to_vec());
        }

        for i in 0..1024 {
            let i0 = i / 256;
            let i1 = i % 256;
            let path = [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,i0 as u8, i1 as u8];
            let triepath = TriePath::from_bytes(&path[..]).unwrap();
            let value = MARF::get(&mut f, &block_header, &triepath).unwrap().unwrap();
            assert_eq!(value.reserved.to_vec(), [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,i0 as u8, i1 as u8].to_vec());
            
            merkle_test(&mut f, &path.to_vec(), &[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,i0 as u8, i1 as u8].to_vec());
        }
        
        dump_trie(&mut f);
    }
    
    #[test]
    fn insert_1024_seq_high() {
        let cursor = Cursor::new(vec![]);
        let mut f = TrieIOBuffer::new(cursor);

        let block_header = BlockHeaderHash::from_bytes(&[0u8; 32]).unwrap();
        MARF::format(&mut f, &block_header).unwrap();

        for i in 0..1024 {
            let i0 = i / 256;
            let i1 = i % 256;
            let path = [i0 as u8, i1 as u8, 2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19];
            let triepath = TriePath::from_bytes(&path[..]).unwrap();
            let value = TrieLeaf::new(&vec![], &[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,i0 as u8, i1 as u8].to_vec());
            MARF::insert(&mut f, &block_header, &triepath, &value).unwrap();
            
            merkle_test(&mut f, &path.to_vec(), &[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,i0 as u8, i1 as u8].to_vec());
        }

        for i in 0..1024 {
            let i0 = i / 256;
            let i1 = i % 256;
            let path = [i0 as u8, i1 as u8, 2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19];
            let triepath = TriePath::from_bytes(&path[..]).unwrap();
            let value = MARF::get(&mut f, &block_header, &triepath).unwrap().unwrap();
            assert_eq!(value.reserved.to_vec(), [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,i0 as u8, i1 as u8].to_vec());

            merkle_test(&mut f, &path.to_vec(), &[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,i0 as u8, i1 as u8].to_vec());
        }
        
        dump_trie(&mut f);
    }
    
    #[test]
    fn insert_1024_seq_mid() {
        let cursor = Cursor::new(vec![]);
        let mut f = TrieIOBuffer::new(cursor);

        let block_header = BlockHeaderHash::from_bytes(&[0u8; 32]).unwrap();
        MARF::format(&mut f, &block_header).unwrap();

        for i in 0..1024 {
            let i0 = i / 256;
            let i1 = (i % 256) / 32;
            let i2 = (i % 256) % 32;
            let i3 = (i % 256) % 16;
            let path = [0,1,i0 as u8,i1 as u8,i2 as u8,i3 as u8,6,7,8,9,10,11,12,13,14,15,16,17,18,19];
            let triepath = TriePath::from_bytes(&path[..]).unwrap();
            let value = TrieLeaf::new(&vec![], &[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,i0 as u8, i1 as u8].to_vec());
            MARF::insert(&mut f, &block_header, &triepath, &value).unwrap();
            
            merkle_test(&mut f, &path.to_vec(), &[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,i0 as u8, i1 as u8].to_vec());
        }

        for i in 0..1024 {
            let i0 = i / 256;
            let i1 = (i % 256) / 32;
            let i2 = (i % 256) % 32;
            let i3 = (i % 256) % 16;
            let path = [0,1,i0 as u8,i1 as u8,i2 as u8,i3 as u8,6,7,8,9,10,11,12,13,14,15,16,17,18,19];
            let triepath = TriePath::from_bytes(&path[..]).unwrap();
            let value = MARF::get(&mut f, &block_header, &triepath).unwrap().unwrap();
            assert_eq!(value.reserved.to_vec(), [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,i0 as u8, i1 as u8].to_vec());

            merkle_test(&mut f, &path.to_vec(), &[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,i0 as u8, i1 as u8].to_vec());
        }
        
        dump_trie(&mut f);
    }
    
    #[test]
    fn insert_65536_random_deterministic() {
        // deterministic random insert of 65536 keys
        let cursor = Cursor::new(vec![]);
        let mut f = TrieIOBuffer::new(cursor);

        let block_header = BlockHeaderHash::from_bytes(&[0u8; 32]).unwrap();
        MARF::format(&mut f, &block_header).unwrap();

        let mut seed = TrieHash::from_data(&[]).as_bytes().to_vec();

        for i in 0..65536 {
            let i0 = i / 256;
            let i1 = i % 256;
            let path = TrieHash::from_data(&seed[..]).as_bytes()[0..20].to_vec();
            seed = path.clone();

            let triepath = TriePath::from_bytes(&path[..]).unwrap();
            let value = TrieLeaf::new(&vec![], &[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,i0 as u8, i1 as u8].to_vec());
            MARF::insert(&mut f, &block_header, &triepath, &value).unwrap();
            
            merkle_test(&mut f, &path.to_vec(), &[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,i0 as u8, i1 as u8].to_vec());
        }

        seed = TrieHash::from_data(&[]).as_bytes().to_vec();

        for i in 0..65536 {
            let i0 = i / 256;
            let i1 = i % 256;
            let path = TrieHash::from_data(&seed[..]).as_bytes()[0..20].to_vec();
            seed = path.clone();
            
            let triepath = TriePath::from_bytes(&path[..]).unwrap();
            let value = MARF::get(&mut f, &block_header, &triepath).unwrap().unwrap();
            assert_eq!(value.reserved.to_vec(), [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,i0 as u8, i1 as u8].to_vec());
            
            merkle_test(&mut f, &path.to_vec(), &[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,i0 as u8, i1 as u8].to_vec());
        }
        
        dump_trie(&mut f);
    }
    
    #[test]
    fn insert_1024_random_deterministic_merkle_proof() {
        // deterministic random insert of 1024 keys
        let cursor = Cursor::new(vec![]);
        let mut f = TrieIOBuffer::new(cursor);

        let block_header = BlockHeaderHash::from_bytes(&[0u8; 32]).unwrap();
        MARF::format(&mut f, &block_header).unwrap();

        let mut seed = TrieHash::from_data(&[]).as_bytes().to_vec();
        
        for i in 0..1024 {
            let i0 = i / 256;
            let i1 = i % 256;
            let path = TrieHash::from_data(&seed[..]).as_bytes()[0..20].to_vec();
            seed = path.clone();

            let triepath = TriePath::from_bytes(&path[..]).unwrap();
            let value = TrieLeaf::new(&vec![], &[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,i0 as u8, i1 as u8].to_vec());
            MARF::insert(&mut f, &block_header, &triepath, &value).unwrap();

            merkle_test(&mut f, &path.to_vec(), &[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,i0 as u8, i1 as u8].to_vec());
        }

        seed = TrieHash::from_data(&[]).as_bytes().to_vec();
        let (_, root_hash) = Trie::read_root(&mut f).unwrap();

        test_debug!("");
        test_debug!("test gets and merkle proofs");
        test_debug!("");

        for i in 0..1024 {
            let i0 = i / 256;
            let i1 = i % 256;
            let path = TrieHash::from_data(&seed[..]).as_bytes()[0..20].to_vec();
            seed = path.clone();
            
            let triepath = TriePath::from_bytes(&path[..]).unwrap();
            let value = MARF::get(&mut f, &block_header, &triepath).unwrap().unwrap();
            assert_eq!(value.reserved.to_vec(), [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,i0 as u8, i1 as u8].to_vec());
            
            merkle_test(&mut f, &path.to_vec(), &[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,i0 as u8, i1 as u8].to_vec());
        }
        
        dump_trie(&mut f);
    }
   
    #[test]
    fn insert_65536_trie_ram_dump() {
        // deterministic random insert of many keys to a TrieRAM, dumped to a TrieIOBuffer
        let block_header = BlockHeaderHash::from_bytes(&[0u8; 32]).unwrap();
        let mut f = TrieRAM::new(&block_header, 1024*1024);

        MARF::format(&mut f, &block_header).unwrap();

        let mut seed = TrieHash::from_data(&[]).as_bytes().to_vec();

        for i in 0..65536 {
            let i0 = i / 256;
            let i1 = i % 256;
            let path = TrieHash::from_data(&seed[..]).as_bytes()[0..20].to_vec();
            seed = path.clone();

            let triepath = TriePath::from_bytes(&path[..]).unwrap();
            let value = TrieLeaf::new(&vec![], &[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,i0 as u8, i1 as u8].to_vec());
            MARF::insert(&mut f, &block_header, &triepath, &value).unwrap();
        }

        seed = TrieHash::from_data(&[]).as_bytes().to_vec();

        // convert to a TrieIOBuffer 
        let mut buf = io::Cursor::new(vec![]);
        f.dump(&mut buf, &block_header, &TrieFileStorage::block_sentinel()).unwrap();

        fseek(&mut buf, 0).unwrap();

        let mut tb = TrieIOBuffer::new(buf);

        // all reads should succeed on the trie IO buffer
        for i in 0..65536 {
            let i0 = i / 256;
            let i1 = i % 256;
            let path = TrieHash::from_data(&seed[..]).as_bytes()[0..20].to_vec();
            seed = path.clone();
            
            let triepath = TriePath::from_bytes(&path[..]).unwrap();
            let value = MARF::get(&mut tb, &block_header, &triepath).unwrap().unwrap();
            assert_eq!(value.reserved.to_vec(), [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,i0 as u8, i1 as u8].to_vec());
            
            merkle_test(&mut tb, &path.to_vec(), &[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,i0 as u8, i1 as u8].to_vec());
        }
    }

    /// Verify that all nodes along a path are _not_ BackPtrs.
    /// Return the TrieCursor from walking down the path
    fn marf_verify_cow<S: TrieStorage + Seek>(s: &mut S, block_header: &BlockHeaderHash, path: &Vec<u8>) -> TrieCursor {
        // walk to insertion point 
        s.open(block_header, false).unwrap();
        let (mut node, _) = Trie::read_root(s).unwrap();
        let mut node_ptr = TriePtr::new(0,0,0);

        let mut c = TrieCursor::new(&TriePath::from_bytes(&path[..]).unwrap(), s.root_ptr());

        for _ in 0..c.path.len()+1 {
            let next_opt = Trie::walk_from(s, &node, &mut c).unwrap();
            match next_opt {
                Some((next_node_ptr, next_node, _)) => {
                    // keep walking 
                    node = next_node;
                    node_ptr = next_node_ptr;
                    continue;
                },
                None => {}
            }
            if c.eop() {
                break;
            }
        }
        c
    }

    #[test]
    fn triefilestorage_extend() {
        let path = "/tmp/rust_triefilestorage_extend".to_string();
        match fs::metadata(&path) {
            Ok(_) => {
                fs::remove_dir_all(&path).unwrap();
            },
            Err(_) => {}
        };
        let mut f = TrieFileStorage::new(&path).unwrap();

        // build a 5-block fork
        for i in 0..5 {
            let bhh = BlockHeaderHash([i as u8; 32]);
            MARF::extend_trie(&mut f, &bhh).unwrap();

            // file must be created
            let block_path = TrieFileStorage::block_path(&f.dir_path, &bhh);
            match fs::metadata(&block_path) {
                Ok(md) => {
                    assert_eq!(md.len(), 32);
                },
                Err(_) => {
                    assert!(false);
                }
            }

            // file must have parent hash
            let parent_hash = TrieFileStorage::read_block_parent(&f.dir_path, &bhh).unwrap();
            if i == 0 {
                assert_eq!(parent_hash, TrieFileStorage::block_sentinel());
            }
            else {
                assert_eq!(parent_hash, BlockHeaderHash([(i - 1) as u8; 32]));
            }
        }

        for i in 0..5 {
            assert!(f.fork_table.contains(&BlockHeaderHash([i as u8; 32])));
        }
        
        for i in 0..5 {
            assert_eq!(f.fork_table.walk_back(&BlockHeaderHash([4u8; 32]), i).unwrap(), BlockHeaderHash([(4 - i) as u8; 32]));
        }

        assert_eq!(f.tell(), BlockHeaderHash([4u8; 32]));
        assert_eq!(f.fork_table.fork_table.len(), 1);

        let mut sorted_chain_tips = f.fork_table.fork_table[0].clone();
        sorted_chain_tips.sort();

        assert_eq!(sorted_chain_tips, vec![BlockHeaderHash([0u8; 32]), BlockHeaderHash([1u8; 32]), BlockHeaderHash([2u8; 32]), BlockHeaderHash([3u8; 32]), BlockHeaderHash([4u8; 32]), TrieFileStorage::block_sentinel()]);

        // re-instantiation will load the fork
        let f2 = TrieFileStorage::new(&path).unwrap();
        assert_eq!(f2.fork_table, f.fork_table);
        
        for i in 0..5 {
            assert!(f2.fork_table.contains(&BlockHeaderHash([i as u8; 32])));
        }
        
        for i in 0..5 {
            assert_eq!(f2.fork_table.walk_back(&BlockHeaderHash([4u8; 32]), i).unwrap(), BlockHeaderHash([(4 - i) as u8; 32]));
        }
    } 
    
    #[test]
    fn triefilestorage_extend_fork_sequence() {
        let path = "/tmp/rust_triefilestorage_extend_fork_sequence".to_string();
        match fs::metadata(&path) {
            Ok(_) => {
                fs::remove_dir_all(&path).unwrap();
            },
            Err(_) => {}
        };
        let mut f = TrieFileStorage::new(&path).unwrap();

        let mut main_fork = vec![TrieFileStorage::block_sentinel()];
        let mut expected_forks : Vec<Vec<BlockHeaderHash>> = vec![];
        let mut expected_chain_tips = vec![];

        for i in 0..5 {
            expected_forks.push(vec![TrieFileStorage::block_sentinel()]);
        }

        for i in 0..5 {
            let bhh = BlockHeaderHash([i as u8; 32]);
            let fork_bhh = BlockHeaderHash([(i + 128) as u8; 32]);

            MARF::extend_trie(&mut f, &bhh).unwrap();
            
            // file must be created
            let block_path = TrieFileStorage::block_path(&f.dir_path, &bhh);
            match fs::metadata(&block_path) {
                Ok(md) => {
                    assert_eq!(md.len(), 32);
                },
                Err(_) => {
                    assert!(false);
                }
            }

            // file must have parent hash
            let parent_hash = TrieFileStorage::read_block_parent(&f.dir_path, &bhh).unwrap();
            if i == 0 {
                assert_eq!(parent_hash, TrieFileStorage::block_sentinel());
            }
            else {
                assert_eq!(parent_hash, BlockHeaderHash([(i - 1) as u8; 32]));
            }

            // make a sibling 1-block fork
            if i > 0 {
                f.open(&parent_hash, true).unwrap();
                MARF::extend_trie(&mut f, &fork_bhh).unwrap();
            
                // file must be created
                let block_path = TrieFileStorage::block_path(&f.dir_path, &fork_bhh);
                match fs::metadata(&block_path) {
                    Ok(md) => {
                        assert_eq!(md.len(), 32);
                    },
                    Err(_) => {
                        assert!(false);
                    }
                }

                // file must have parent hash
                let parent_hash = TrieFileStorage::read_block_parent(&f.dir_path, &fork_bhh).unwrap();
                assert_eq!(parent_hash, BlockHeaderHash([(i - 1) as u8; 32]));

                expected_chain_tips.push(fork_bhh);
            }

            f.open(&bhh, true).unwrap();

            if i > 0 {
                expected_forks[i] = main_fork.clone();
                expected_forks[i].push(fork_bhh);
            }
            
            main_fork.push(bhh);
        }
        
        expected_forks[0] = main_fork.clone();

        expected_chain_tips.push(f.tell());

        test_debug!("fork table:\n{:#?}", &f.fork_table);

        let mut chain_tips = f.fork_table.chain_tips();

        expected_chain_tips.sort();
        chain_tips.sort();
        assert_eq!(expected_chain_tips, chain_tips);
        
        test_debug!("chain tips: {:?}", chain_tips);
        test_debug!("expected forks:\n{:#?}", &expected_forks);

        // all parent blocks are reachable from each non-root
        for expected_fork in expected_forks.iter() {
            for j in 0..expected_fork.len() {
                let chain_tip = expected_fork[expected_fork.len() - j - 1].clone();
                for i in 0..expected_fork.len()-j {
                    let k = expected_fork.len() - j - 1 - i;
                    test_debug!("Walk from {:?} back {} to {:?}", &chain_tip, k, &expected_fork[i]);
                    let parent_bhh = f.fork_table.walk_back(&chain_tip, k as u32).unwrap();
                    assert_eq!(parent_bhh, expected_fork[i]);
                }
            }
        }
        
        // re-instantiation will load the fork
        let f2 = TrieFileStorage::new(&path).unwrap();

        test_debug!("fork table 1:\n{:#?}", &f.fork_table);
        test_debug!("fork table 2:\n{:#?}", &f2.fork_table);

        assert_eq!(f2.fork_table, f.fork_table);
        
        // all parent blocks are reachable from each non-root
        for expected_fork in expected_forks.iter() {
            for j in 0..expected_fork.len() {
                let chain_tip = expected_fork[expected_fork.len() - j - 1].clone();
                for i in 0..expected_fork.len()-j {
                    let k = expected_fork.len() - j - 1 - i;
                    test_debug!("Walk from {:?} back {} to {:?}", &chain_tip, k, &expected_fork[i]);
                    let parent_bhh = f2.fork_table.walk_back(&chain_tip, k as u32).unwrap();
                    assert_eq!(parent_bhh, expected_fork[i]);
                }
            }
        }
    }

    #[test]
    fn triefilestorage_extend_fork_5_len_3() {
        let path = "/tmp/rust_triefilestorage_extend_fork_5_len_3".to_string();
        match fs::metadata(&path) {
            Ok(_) => {
                fs::remove_dir_all(&path).unwrap();
            },
            Err(_) => {}
        };
        let mut f = TrieFileStorage::new(&path).unwrap();

        let mut expected_forks : Vec<Vec<BlockHeaderHash>> = vec![];
        let mut expected_root_fork = vec![];

        expected_root_fork.push(TrieFileStorage::block_sentinel());

        // build a 5-block fork...
        for i in 0..5 {
            let bhh = BlockHeaderHash([i as u8; 32]);
            expected_root_fork.push(bhh.clone());

            MARF::extend_trie(&mut f, &bhh).unwrap();

            // file must be created
            let block_path = TrieFileStorage::block_path(&f.dir_path, &bhh);
            match fs::metadata(&block_path) {
                Ok(md) => {
                    assert_eq!(md.len(), 32);
                },
                Err(_) => {
                    assert!(false);
                }
            }

            // file must have parent hash
            let parent_hash = TrieFileStorage::read_block_parent(&f.dir_path, &bhh).unwrap();
            if i == 0 {
                assert_eq!(parent_hash, TrieFileStorage::block_sentinel());
            }
            else {
                assert_eq!(parent_hash, BlockHeaderHash([(i - 1) as u8; 32]));
            }
        }

        for i in 0..5 {
            expected_forks.push(expected_root_fork.clone());
        }

        // build 5 additional 3-block forks off of it
        for i in 0..5 {
            f.open(&BlockHeaderHash([4u8; 32]), false).unwrap();

            for j in 0..3 {
                let bhh = BlockHeaderHash([(3*(i+5) + j) as u8; 32]);
                expected_forks[i].push(bhh);

                MARF::extend_trie(&mut f, &bhh).unwrap();

                // file must be created
                let block_path = TrieFileStorage::block_path(&f.dir_path, &bhh);
                match fs::metadata(&block_path) {
                    Ok(md) => {
                        assert_eq!(md.len(), 32);
                    },
                    Err(_) => {
                        assert!(false);
                    }
                }

                // file must have parent hash
                let parent_hash = TrieFileStorage::read_block_parent(&f.dir_path, &bhh).unwrap();
                if j == 0 {
                    // common ancestor of all 3 forks
                    assert_eq!(parent_hash, BlockHeaderHash([4u8; 32]));
                }
                else {
                    assert_eq!(parent_hash, BlockHeaderHash([(3*(i+5) + j - 1) as u8; 32]));
                }
            }
        }

        test_debug!("fork table = \n{:#?}", &f.fork_table);
        assert_eq!(f.fork_table.fork_table.len(), 5);
        let chain_tips = f.fork_table.chain_tips();
        assert_eq!(chain_tips.len(), 5);

        assert_eq!(chain_tips, vec![
                   BlockHeaderHash([17u8; 32]), 
                   BlockHeaderHash([20u8; 32]), 
                   BlockHeaderHash([23u8; 32]),
                   BlockHeaderHash([26u8; 32]),
                   BlockHeaderHash([29u8; 32])
                ]);

        for (j, chain_tip) in chain_tips.iter().enumerate() {
            // we can walk back all the way to the root from each chain tip
            for i in 0..9 {
                test_debug!("walk {:?} back {} to {:?}?", chain_tip, 8 - i, expected_forks[j][i as usize]);
                let bh = f.fork_table.walk_back(chain_tip, 8 - i).unwrap();
                assert_eq!(expected_forks[j][i as usize], bh);
            }
        }

        // re-instantiation will load the fork
        let f2 = TrieFileStorage::new(&path).unwrap();

        test_debug!("fork table 1:\n{:#?}", &f.fork_table);
        test_debug!("fork table 2:\n{:#?}", &f2.fork_table);

        assert_eq!(f2.fork_table, f.fork_table);

        for (j, chain_tip) in chain_tips.iter().enumerate() {
            // we can walk back all the way to the root from each chain tip in the loaded fork
            for i in 0..9 {
                test_debug!("walk {:?} back {} to {:?}?", chain_tip, 8 - i, expected_forks[j][i as usize]);
                let bh = f2.fork_table.walk_back(chain_tip, 8 - i).unwrap();
                assert_eq!(expected_forks[j][i as usize], bh);
            }
        }

        // all parent blocks are reachable from all non-root blocks
        for s in [f, f2].iter() {
            for expected_fork in expected_forks.iter() {
                for j in 0..expected_fork.len() {
                    let chain_tip = expected_fork[expected_fork.len() - j - 1].clone();
                    for i in 0..expected_fork.len()-j {
                        let k = expected_fork.len() - j - 1 - i;
                        test_debug!("Walk from {:?} back {} to {:?}", &chain_tip, k, &expected_fork[i]);
                        let parent_bhh = s.fork_table.walk_back(&chain_tip, k as u32).unwrap();
                        assert_eq!(parent_bhh, expected_fork[i]);
                    }
                }
            }
        }
    } 

    #[test]
    fn marf_extend_trie() {
        let cursor = Cursor::new(vec![]);
        let mut f = TrieIOBuffer::new(cursor);

        let block_header_1 = BlockHeaderHash::from_bytes(&[0u8; 32]).unwrap();
        MARF::format(&mut f, &block_header_1).unwrap();

        for i in 1..9 {
            let cur_block_header = BlockHeaderHash::from_bytes(&[i as u8; 32]).unwrap();
            let prev_block_header = BlockHeaderHash::from_bytes(&[(i - 1) as u8; 32]).unwrap();

            f.open(&prev_block_header, true).unwrap();
            MARF::extend_trie(&mut f, &cur_block_header).unwrap();

            assert_eq!(f.tell(), cur_block_header);

            let (root, _) = Trie::read_root(&mut f).unwrap();
            match root {
                TrieNodeType::Node256(ref data) => {
                    /*
                    assert_eq!(data.backptrs.len() as u64, log2_floor(i)+1);

                    for idx in 0..data.backptrs.len() {
                        let j = i - (1 << idx);
                        let expected_header = BlockHeaderHash::from_bytes(&[j as u8; 32]).unwrap();
                        assert_eq!(data.backptrs[idx].block_hash, expected_header);
                        assert_eq!(data.backptrs[idx].ptr.ptr, 0);

                        if j == 0 {
                            assert_eq!(data.backptrs[idx].ptr.id, TrieNodeID::Node256);
                        }
                        else {
                            assert_eq!(data.backptrs[idx].ptr.id, set_backptr(TrieNodeID::Node256));
                        }
                    }
                    */
                },
                _ => {
                    assert!(false);
                }
            }
        }
    }
    
    #[test]
    fn marf_insert_different_leaf_same_block_100() {
        let path = "/tmp/rust_marf_insert_different_leaf_same_block_100".to_string();
        match fs::metadata(&path) {
            Ok(_) => {
                fs::remove_dir_all(&path).unwrap();
            },
            Err(_) => {}
        };
        let mut f = TrieFileStorage::new(&path).unwrap();

        let block_header_1 = BlockHeaderHash::from_bytes(&[0u8; 32]).unwrap();
        MARF::format(&mut f, &block_header_1).unwrap();

        let path_bytes = [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19];
        let path = TriePath::from_bytes(&path_bytes).unwrap();
        let block_header = BlockHeaderHash::from_bytes(&[0; 32]).unwrap();

        for i in 0..100 {
            let value = TrieLeaf::new(&vec![], &[i as u8; 40].to_vec());
            MARF::insert(&mut f, &block_header, &path, &value).unwrap();
        }
        
        test_debug!("---------");
        test_debug!("MARF gets");
        test_debug!("---------");

        let value = TrieLeaf::new(&vec![], &[99; 40].to_vec());
        let leaf = MARF::get(&mut f, &block_header, &path).unwrap().unwrap();

        assert_eq!(leaf.reserved.to_vec(), [99; 40].to_vec());
        assert_eq!(f.tell(), block_header);

        merkle_test_marf(&mut f, &block_header, &path_bytes.to_vec(), &[99; 40].to_vec());
    }
    
    #[test]
    fn marf_insert_different_leaf_different_path_different_block_100() {
        let path = "/tmp/rust_marf_insert_different_leaf_different_path_different_block_100".to_string();
        match fs::metadata(&path) {
            Ok(_) => {
                fs::remove_dir_all(&path).unwrap();
            },
            Err(_) => {}
        };
        let mut f = TrieFileStorage::new(&path).unwrap();

        let block_header_1 = BlockHeaderHash::from_bytes(&[0u8; 32]).unwrap();
        MARF::format(&mut f, &block_header_1).unwrap();

        for i in 0..100 {
            test_debug!("insert {}", i);
            let block_header = BlockHeaderHash::from_bytes(&[i as u8; 32]).unwrap();
            let path_bytes = [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,i as u8];
            let path = TriePath::from_bytes(&path_bytes).unwrap();
            let value = TrieLeaf::new(&vec![], &[i as u8; 40].to_vec());
            MARF::insert(&mut f, &block_header, &path, &value).unwrap();
        }
        
        test_debug!("---------");
        test_debug!("MARF gets");
        test_debug!("---------");

        for i in 0..100 {
            let block_header = BlockHeaderHash::from_bytes(&[i as u8; 32]).unwrap();
            let path_bytes = [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,i as u8];
            let path = TriePath::from_bytes(&path_bytes).unwrap();

            let value = TrieLeaf::new(&vec![], &[i as u8; 40].to_vec());
            let leaf = MARF::get(&mut f, &block_header, &path).unwrap().unwrap();

            assert_eq!(leaf.reserved.to_vec(), [i as u8; 40].to_vec());
            assert_eq!(f.tell(), block_header);

            merkle_test_marf(&mut f, &block_header, &path_bytes.to_vec(), &[i as u8; 40].to_vec());
        }
    }

    #[test]
    fn marf_insert_same_leaf_different_block_100() {
        let path = "/tmp/rust_marf_same_leaf_different_block_100".to_string();
        match fs::metadata(&path) {
            Ok(_) => {
                fs::remove_dir_all(&path).unwrap();
            },
            Err(_) => {}
        };
        let mut f = TrieFileStorage::new(&path).unwrap();

        let block_header_1 = BlockHeaderHash::from_bytes(&[0u8; 32]).unwrap();
        MARF::format(&mut f, &block_header_1).unwrap();

        let path_bytes = [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19];
        let path = TriePath::from_bytes(&path_bytes).unwrap();

        for i in 0..100 {
            let next_block_header = BlockHeaderHash::from_bytes(&[i as u8; 32]).unwrap();
            let value = TrieLeaf::new(&vec![], &[i as u8; 40].to_vec());
            MARF::insert(&mut f, &next_block_header, &path, &value).unwrap();
        }
        
        test_debug!("---------");
        test_debug!("MARF gets");
        test_debug!("---------");

        for i in 0..100 {
            let next_block_header = BlockHeaderHash::from_bytes(&[i as u8; 32]).unwrap();
            let value = TrieLeaf::new(&vec![], &[i as u8; 40].to_vec());
            let leaf = MARF::get(&mut f, &next_block_header, &path).unwrap().unwrap();

            assert_eq!(leaf.reserved.to_vec(), [i as u8; 40].to_vec());
            assert_eq!(f.tell(), next_block_header);

            merkle_test_marf(&mut f, &next_block_header, &path_bytes.to_vec(), &[i as u8; 40].to_vec());
        }
    }
    
    #[test]
    fn marf_insert_leaf_sequence_2() {
        let path = "/tmp/rust_marf_insert_leaf_sequence_2".to_string();
        match fs::metadata(&path) {
            Ok(_) => {
                fs::remove_dir_all(&path).unwrap();
            },
            Err(_) => {}
        };
        let mut f = TrieFileStorage::new(&path).unwrap();

        let block_header_1 = BlockHeaderHash::from_bytes(&[0u8; 32]).unwrap();
        MARF::format(&mut f, &block_header_1).unwrap();

        for i in 0..2 {
            let path_bytes = [i as u8,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19];
            let path = TriePath::from_bytes(&path_bytes).unwrap();

            let next_block_header = BlockHeaderHash::from_bytes(&[i as u8; 32]).unwrap();
            let value = TrieLeaf::new(&vec![], &[i as u8; 40].to_vec());
            MARF::insert(&mut f, &next_block_header, &path, &value).unwrap();
        }
        
        let last_block_header = BlockHeaderHash::from_bytes(&[1; 32]).unwrap();

        test_debug!("---------");
        test_debug!("MARF gets");
        test_debug!("---------");

        for i in 0..2 {
            let next_block_header = BlockHeaderHash::from_bytes(&[i as u8; 32]).unwrap();
            let path_bytes = [i as u8,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19];
            let path = TriePath::from_bytes(&path_bytes).unwrap();
            
            let value = TrieLeaf::new(&vec![], &[i as u8; 40].to_vec());
            let leaf = MARF::get(&mut f, &last_block_header, &path).unwrap().unwrap();

            assert_eq!(leaf.reserved.to_vec(), [i as u8; 40].to_vec());
            assert_eq!(f.tell(), next_block_header);

            merkle_test_marf(&mut f, &last_block_header, &path_bytes.to_vec(), &[i as u8; 40].to_vec());
        }
    }
    
    #[test]
    fn marf_insert_leaf_sequence_100() {
        let path = "/tmp/rust_marf_insert_leaf_sequence_100".to_string();
        match fs::metadata(&path) {
            Ok(_) => {
                fs::remove_dir_all(&path).unwrap();
            },
            Err(_) => {}
        };
        let mut f = TrieFileStorage::new(&path).unwrap();

        let block_header_1 = BlockHeaderHash::from_bytes(&[0u8; 32]).unwrap();
        MARF::format(&mut f, &block_header_1).unwrap();

        for i in 0..100 {
            let path_bytes = [i as u8,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19];
            let path = TriePath::from_bytes(&path_bytes).unwrap();

            let next_block_header = BlockHeaderHash::from_bytes(&[i as u8; 32]).unwrap();
            let value = TrieLeaf::new(&vec![], &[i as u8; 40].to_vec());
            MARF::insert(&mut f, &next_block_header, &path, &value).unwrap();
        }
        
        let last_block_header = BlockHeaderHash::from_bytes(&[99; 32]).unwrap();

        test_debug!("---------");
        test_debug!("MARF gets");
        test_debug!("---------");

        for i in 0..100 {
            let next_block_header = BlockHeaderHash::from_bytes(&[i as u8; 32]).unwrap();
            let path_bytes = [i as u8,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19];
            let path = TriePath::from_bytes(&path_bytes).unwrap();
            
            let value = TrieLeaf::new(&vec![], &[i as u8; 40].to_vec());
            let leaf = MARF::get(&mut f, &last_block_header, &path).unwrap().unwrap();

            assert_eq!(leaf.reserved.to_vec(), [i as u8; 40].to_vec());
            assert_eq!(f.tell(), next_block_header);

            merkle_test_marf(&mut f, &last_block_header, &path_bytes.to_vec(), &[i as u8; 40].to_vec());
        }
    }

    #[test]
    fn marf_walk_cow_node4_20() {
        let path = "/tmp/rust_marf_walk_cow_node4_20".to_string();
        match fs::metadata(&path) {
            Ok(_) => {
                fs::remove_dir_all(&path).unwrap();
            },
            Err(_) => {}
        };
        let mut f = TrieFileStorage::new(&path).unwrap();

        let block_header_1 = BlockHeaderHash::from_bytes(&[0u8; 32]).unwrap();
        MARF::format(&mut f, &block_header_1).unwrap();

        // make a deep path
        let path_segments = vec![
            (vec![], 0),
            (vec![], 1),
            (vec![], 2),
            (vec![], 3),
            (vec![], 4),
            (vec![], 5),
            (vec![], 6),
            (vec![], 7),
            (vec![], 8),
            (vec![], 9),
            (vec![], 10),
            (vec![], 11),
            (vec![], 12),
            (vec![], 13),
            (vec![], 14),
            (vec![], 15),
            (vec![], 16),
            (vec![], 17),
            (vec![], 18),
            (vec![], 19)
        ];
        let path = vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19];

        let (nodes, node_ptrs, hashes) = make_node4_path(&mut f, &path_segments, [19u8; 40].to_vec());
        dump_trie(&mut f);

        for i in 1..19 {
            test_debug!("----------------");
            test_debug!("i = {}", i);
            test_debug!("----------------");

            // switch to the next block
            let next_block_header = BlockHeaderHash::from_bytes(&[i as u8; 32]).unwrap();

            // add a leaf at the end of the path
            let mut next_path = path.clone();
            next_path[i] = 20;
            
            let triepath = TriePath::from_bytes(&next_path[..]).unwrap();
            let value = TrieLeaf::new(&vec![], &[i as u8; 40].to_vec());
            
            test_debug!("----------------");
            test_debug!("insert");
            test_debug!("----------------");
            MARF::insert(&mut f, &next_block_header, &triepath, &value).unwrap();

            // verify that this leaf exists in _this_ Trie
            test_debug!("----------------");
            test_debug!("get");
            test_debug!("----------------");
            let read_value = MARF::get(&mut f, &next_block_header, &TriePath::from_bytes(&next_path[..]).unwrap()).unwrap().unwrap();
            assert_eq!(read_value.reserved.to_vec(), [i as u8; 40].to_vec());
            assert_eq!(read_value.path, next_path[i+1..].to_vec());
            assert_eq!(f.tell(), next_block_header);

            // can get all previous leaves from _this_ Trie
            for j in 1..(i+1) {
                test_debug!("----------------");
                test_debug!("get-prev {} of {}", j, i);
                test_debug!("----------------");

                let mut prev_path = path.clone();
                prev_path[j] = 20;
            
                let prev_block_header = BlockHeaderHash::from_bytes(&[j as u8; 32]).unwrap();

                let read_value = MARF::get(&mut f, &next_block_header, &TriePath::from_bytes(&prev_path[..]).unwrap()).unwrap().unwrap();
                assert_eq!(read_value.reserved.to_vec(), [j as u8; 40].to_vec());
                assert_eq!(f.tell(), prev_block_header);
            }

            f.open(&next_block_header, false).unwrap();

            test_debug!("----------------");
            test_debug!("MARF verify cow");
            test_debug!("----------------");

            let c = marf_verify_cow(&mut f, &next_block_header, &next_path);
            let mut leaf_count = 0;
            for node in c.nodes.iter() {
                let ptrs = match node {
                    TrieNodeType::Node4(ref data) => data.ptrs.to_vec(),
                    TrieNodeType::Node16(ref data) => data.ptrs.to_vec(),
                    TrieNodeType::Node48(ref data) => data.ptrs.to_vec(),
                    TrieNodeType::Node256(ref data) => data.ptrs.to_vec(),
                    TrieNodeType::Leaf(_) => vec![],
                };
                for ptr in ptrs {
                    if ptr.id() == TrieNodeID::Leaf {
                        leaf_count += 1;
                    }
                }
            }

            dump_trie(&mut f);

            // only one leaf in this trie
            assert_eq!(leaf_count, 1);
           
            merkle_test_marf(&mut f, &next_block_header, &next_path, &[i as u8; 40].to_vec());
        }

        // all leaves are reachable from the last block 
        let last_block_header = BlockHeaderHash::from_bytes(&[18u8; 32]).unwrap();
        for i in 1..19 {
            // add a leaf at the end of the path
            let mut next_path = path.clone();
            next_path[i] = 20;
            
            let triepath = TriePath::from_bytes(&next_path[..]).unwrap();
            let value = TrieLeaf::new(&next_path[i+1..].to_vec(), &[i as u8; 40].to_vec());

            assert_eq!(MARF::get(&mut f, &last_block_header, &triepath).unwrap(), Some(value));
            
            merkle_test_marf(&mut f, &last_block_header, &next_path, &[i as u8; 40].to_vec());
        }
    }

    #[test]
    fn marf_walk_cow_node4_20_reversed() {
        let path = "/tmp/rust_marf_walk_cow_node4_20_reversed".to_string();
        match fs::metadata(&path) {
            Ok(_) => {
                fs::remove_dir_all(&path).unwrap();
            },
            Err(_) => {}
        };
        let mut f = TrieFileStorage::new(&path).unwrap();

        let block_header_1 = BlockHeaderHash::from_bytes(&[0u8; 32]).unwrap();
        MARF::format(&mut f, &block_header_1).unwrap();

        // make a deep path
        let path_segments = vec![
            (vec![], 0),
            (vec![], 1),
            (vec![], 2),
            (vec![], 3),
            (vec![], 4),
            (vec![], 5),
            (vec![], 6),
            (vec![], 7),
            (vec![], 8),
            (vec![], 9),
            (vec![], 10),
            (vec![], 11),
            (vec![], 12),
            (vec![], 13),
            (vec![], 14),
            (vec![], 15),
            (vec![], 16),
            (vec![], 17),
            (vec![], 18),
            (vec![], 19)
        ];
        let path = vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19];

        let (nodes, node_ptrs, hashes) = make_node4_path(&mut f, &path_segments, [19u8; 40].to_vec());
        dump_trie(&mut f);

        for i in 1..19 {
            test_debug!("----------------");
            test_debug!("i = {}", i);
            test_debug!("----------------");

            // switch to the next block
            let next_block_header = BlockHeaderHash::from_bytes(&[i as u8; 32]).unwrap();

            // add a leaf at the end of the path
            let mut next_path = path.clone();
            next_path[19 - i] = 20;
            
            let triepath = TriePath::from_bytes(&next_path[..]).unwrap();
            let value = TrieLeaf::new(&vec![], &[i as u8; 40].to_vec());
            
            test_debug!("----------------");
            test_debug!("insert");
            test_debug!("----------------");
            MARF::insert(&mut f, &next_block_header, &triepath, &value).unwrap();

            // verify that this leaf exists in _this_ Trie
            test_debug!("----------------");
            test_debug!("get");
            test_debug!("----------------");
            let read_value = MARF::get(&mut f, &next_block_header, &TriePath::from_bytes(&next_path[..]).unwrap()).unwrap().unwrap();
            assert_eq!(read_value.reserved.to_vec(), [i as u8; 40].to_vec());
            assert_eq!(read_value.path, next_path[19-i+1..].to_vec());
            assert_eq!(f.tell(), next_block_header);

            // can get all previous leaves from _this_ Trie
            for j in 1..(i+1) {
                test_debug!("----------------");
                test_debug!("get-prev {} of {}", j, i);
                test_debug!("----------------");

                let mut prev_path = path.clone();
                prev_path[19-j] = 20;
            
                let prev_block_header = BlockHeaderHash::from_bytes(&[j as u8; 32]).unwrap();

                let read_value = MARF::get(&mut f, &next_block_header, &TriePath::from_bytes(&prev_path[..]).unwrap()).unwrap().unwrap();
                assert_eq!(read_value.reserved.to_vec(), [j as u8; 40].to_vec());
                assert_eq!(f.tell(), prev_block_header);
            }

            f.open(&next_block_header, false).unwrap();

            test_debug!("----------------");
            test_debug!("MARF verify cow");
            test_debug!("----------------");

            let c = marf_verify_cow(&mut f, &next_block_header, &next_path);
            let mut leaf_count = 0;
            for node in c.nodes.iter() {
                let ptrs = match node {
                    TrieNodeType::Node4(ref data) => data.ptrs.to_vec(),
                    TrieNodeType::Node16(ref data) => data.ptrs.to_vec(),
                    TrieNodeType::Node48(ref data) => data.ptrs.to_vec(),
                    TrieNodeType::Node256(ref data) => data.ptrs.to_vec(),
                    TrieNodeType::Leaf(_) => vec![],
                };
                for ptr in ptrs {
                    if ptr.id() == TrieNodeID::Leaf {
                        leaf_count += 1;
                    }
                }
            }

            dump_trie(&mut f);

            // only one leaf in this trie
            assert_eq!(leaf_count, 1);
            
            merkle_test_marf(&mut f, &next_block_header, &next_path, &[i as u8; 40].to_vec());
        }

        // all leaves are reachable from the last block 
        let last_block_header = BlockHeaderHash::from_bytes(&[18u8; 32]).unwrap();
        for i in 1..19 {
            // add a leaf at the end of the path
            let mut next_path = path.clone();
            next_path[19-i] = 20;
            
            let triepath = TriePath::from_bytes(&next_path[..]).unwrap();
            let value = TrieLeaf::new(&next_path[19-i+1..].to_vec(), &[i as u8; 40].to_vec());

            assert_eq!(MARF::get(&mut f, &last_block_header, &triepath).unwrap(), Some(value));
            
            merkle_test_marf(&mut f, &last_block_header, &next_path, &[i as u8; 40].to_vec());
        }
    }

    #[test]
    fn marf_walk_cow_4() {
        for node_id in [TrieNodeID::Node4, TrieNodeID::Node16, TrieNodeID::Node48, TrieNodeID::Node256].iter() {
            let path = format!("/tmp/rust_marf_walk_cow_node4_20_reversed-{}", node_id);
            match fs::metadata(&path) {
                Ok(_) => {
                    fs::remove_dir_all(&path).unwrap();
                },
                Err(_) => {}
            };
            let mut f = TrieFileStorage::new(&path).unwrap();

            let block_header_1 = BlockHeaderHash::from_bytes(&[0u8; 32]).unwrap();
            MARF::format(&mut f, &block_header_1).unwrap();

            let path_segments = vec![
                (vec![0,1,2,3], 4),
                (vec![5,6,7,8], 9),
                (vec![10,11,12,13], 14),
                (vec![15,16,17,18], 19)
            ];
            let path = vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19];

            let (nodes, node_ptrs, hashes) = make_node_path(&mut f, *node_id, &path_segments, [19u8; 40].to_vec());
            dump_trie(&mut f);

            for i in 1..19 {
                test_debug!("----------------");
                test_debug!("i = {}", i);
                test_debug!("----------------");

                // switch to the next block
                let next_block_header = BlockHeaderHash::from_bytes(&[i as u8; 32]).unwrap();

                // add a leaf at the end of the path
                let mut next_path = path.clone();
                next_path[i] = 20;
                
                let triepath = TriePath::from_bytes(&next_path[..]).unwrap();
                let value = TrieLeaf::new(&vec![], &[i as u8; 40].to_vec());
                
                test_debug!("----------------");
                test_debug!("insert");
                test_debug!("----------------");
                MARF::insert(&mut f, &next_block_header, &triepath, &value).unwrap();

                // verify that this leaf exists in _this_ Trie
                test_debug!("----------------");
                test_debug!("get");
                test_debug!("----------------");
                let read_value = MARF::get(&mut f, &next_block_header, &TriePath::from_bytes(&next_path[..]).unwrap()).unwrap().unwrap();
                assert_eq!(read_value.reserved.to_vec(), [i as u8; 40].to_vec());
                assert_eq!(read_value.path, next_path[i+1..].to_vec());
                assert_eq!(f.tell(), next_block_header);

                // can get all previous leaves from _this_ Trie
                for j in 1..(i+1) {
                    test_debug!("----------------");
                    test_debug!("get-prev {} of {}", j, i);
                    test_debug!("----------------");

                    let mut prev_path = path.clone();
                    prev_path[j] = 20;
                
                    let prev_block_header = BlockHeaderHash::from_bytes(&[j as u8; 32]).unwrap();

                    let read_value = MARF::get(&mut f, &next_block_header, &TriePath::from_bytes(&prev_path[..]).unwrap()).unwrap().unwrap();
                    assert_eq!(read_value.reserved.to_vec(), [j as u8; 40].to_vec());
                    assert_eq!(f.tell(), prev_block_header);
                }

                f.open(&next_block_header, false).unwrap();

                test_debug!("----------------");
                test_debug!("MARF verify cow");
                test_debug!("----------------");

                let c = marf_verify_cow(&mut f, &next_block_header, &next_path);
                let mut leaf_count = 0;
                for node in c.nodes.iter() {
                    let ptrs = match node {
                        TrieNodeType::Node4(ref data) => data.ptrs.to_vec(),
                        TrieNodeType::Node16(ref data) => data.ptrs.to_vec(),
                        TrieNodeType::Node48(ref data) => data.ptrs.to_vec(),
                        TrieNodeType::Node256(ref data) => data.ptrs.to_vec(),
                        TrieNodeType::Leaf(_) => vec![],
                    };
                    for ptr in ptrs {
                        if ptr.id() == TrieNodeID::Leaf {
                            leaf_count += 1;
                        }
                    }
                }

                dump_trie(&mut f);

                // only one leaf in this trie
                assert_eq!(leaf_count, 1);
                
                merkle_test_marf(&mut f, &next_block_header, &next_path, &[i as u8; 40].to_vec());
            }

            // all leaves are reachable from the last block 
            let last_block_header = BlockHeaderHash::from_bytes(&[18u8; 32]).unwrap();
            for i in 1..19 {
                // add a leaf at the end of the path
                let mut next_path = path.clone();
                next_path[i] = 20;
                
                let triepath = TriePath::from_bytes(&next_path[..]).unwrap();
                let value = TrieLeaf::new(&next_path[i+1..].to_vec(), &[i as u8; 40].to_vec());

                assert_eq!(MARF::get(&mut f, &last_block_header, &triepath).unwrap(), Some(value));
                
                merkle_test_marf(&mut f, &last_block_header, &next_path, &[i as u8; 40].to_vec());
            }
        }
    }
    
    #[test]
    fn marf_merkle_verify_backptrs() {
        for node_id in [TrieNodeID::Node4, TrieNodeID::Node16, TrieNodeID::Node48, TrieNodeID::Node256].iter() {
            let path = format!("/tmp/rust_marf_merkle_verify_backptrs-{}", node_id);
            match fs::metadata(&path) {
                Ok(_) => {
                    fs::remove_dir_all(&path).unwrap();
                },
                Err(_) => {}
            };
            let mut f = TrieFileStorage::new(&path).unwrap();

            let block_header_1 = BlockHeaderHash::from_bytes(&[0u8; 32]).unwrap();
            MARF::format(&mut f, &block_header_1).unwrap();

            let path_segments = vec![
                (vec![0,1,2,3,4,5,6,7,8,9,10,11], 12),
                (vec![13,14,15,16,17,18], 19),
            ];
            
            let path = vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19];

            let (nodes, node_ptrs, hashes) = make_node_path(&mut f, *node_id, &path_segments, [19u8; 40].to_vec());
            dump_trie(&mut f);

            let block_header_2 = BlockHeaderHash::from_bytes(&[1u8; 32]).unwrap();
            let path_2 = vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,20];
            
            test_debug!("----------------");
            test_debug!("Extend to {:?}", block_header_2);
            test_debug!("----------------");

            MARF::insert(&mut f, &block_header_2, &TriePath::from_bytes(&path_2[..]).unwrap(), &TrieLeaf::new(&vec![], &[20 as u8; 40].to_vec())).unwrap();
            
            let block_header_3 = BlockHeaderHash::from_bytes(&[2u8; 32]).unwrap();
            let path_3 = vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,21];
            
            test_debug!("----------------");
            test_debug!("Extend to {:?}", block_header_3);
            test_debug!("----------------");

            MARF::insert(&mut f, &block_header_3, &TriePath::from_bytes(&path_3[..]).unwrap(), &TrieLeaf::new(&vec![], &[21 as u8; 40].to_vec())).unwrap();

            test_debug!("----------------");
            test_debug!("MARF at {:?}", &block_header_1);
            test_debug!("----------------");
            f.open(&block_header_1, false).unwrap();
            dump_trie(&mut f);

            test_debug!("----------------");
            test_debug!("MARF at {:?}", &block_header_2);
            test_debug!("----------------");
            f.open(&block_header_2, false).unwrap();
            dump_trie(&mut f);


            test_debug!("----------------");
            test_debug!("MARF at {:?}", &block_header_3);
            test_debug!("----------------");
            f.open(&block_header_3, false).unwrap();
            dump_trie(&mut f);

            test_debug!("----------------");
            test_debug!("Merkle verify {:?} from {:?}", &to_hex(&[21 as u8; 40]), block_header_3);
            test_debug!("----------------");

            merkle_test_marf(&mut f, &block_header_3, &path_3, &[21 as u8; 40].to_vec());
        }
    }

    #[test]
    fn marf_walk_cow_4_reversed() {
        for node_id in [TrieNodeID::Node4, TrieNodeID::Node16, TrieNodeID::Node48, TrieNodeID::Node256].iter() {
            let path = format!("/tmp/rust_marf_walk_cow_4_reversed-{}", node_id);
            match fs::metadata(&path) {
                Ok(_) => {
                    fs::remove_dir_all(&path).unwrap();
                },
                Err(_) => {}
            };
            let mut f = TrieFileStorage::new(&path).unwrap();

            let block_header_1 = BlockHeaderHash::from_bytes(&[0u8; 32]).unwrap();
            MARF::format(&mut f, &block_header_1).unwrap();

            let path_segments = vec![
                (vec![0,1,2,3], 4),
                (vec![5,6,7,8], 9),
                (vec![10,11,12,13], 14),
                (vec![15,16,17,18], 19)
            ];
            let path = vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19];

            let (nodes, node_ptrs, hashes) = make_node_path(&mut f, *node_id, &path_segments, [19u8; 40].to_vec());
            dump_trie(&mut f);

            for i in 1..19 {
                test_debug!("----------------");
                test_debug!("i = {}", i);
                test_debug!("----------------");

                // switch to the next block
                let next_block_header = BlockHeaderHash::from_bytes(&[i as u8; 32]).unwrap();

                // add a leaf at the end of the path
                let mut next_path = path.clone();
                next_path[19 - i] = 20;
                
                let triepath = TriePath::from_bytes(&next_path[..]).unwrap();
                let value = TrieLeaf::new(&vec![], &[i as u8; 40].to_vec());
                
                test_debug!("----------------");
                test_debug!("insert");
                test_debug!("----------------");
                MARF::insert(&mut f, &next_block_header, &triepath, &value).unwrap();

                // verify that this leaf exists in _this_ Trie
                test_debug!("----------------");
                test_debug!("get");
                test_debug!("----------------");
                let read_value = MARF::get(&mut f, &next_block_header, &TriePath::from_bytes(&next_path[..]).unwrap()).unwrap().unwrap();
                assert_eq!(read_value.reserved.to_vec(), [i as u8; 40].to_vec());
                assert_eq!(read_value.path, next_path[19-i+1..].to_vec());
                assert_eq!(f.tell(), next_block_header);

                // can get all previous leaves from _this_ Trie
                for j in 1..(i+1) {
                    test_debug!("----------------");
                    test_debug!("get-prev {} of {}", j, i);
                    test_debug!("----------------");

                    let mut prev_path = path.clone();
                    prev_path[19-j] = 20;
                
                    let prev_block_header = BlockHeaderHash::from_bytes(&[j as u8; 32]).unwrap();

                    let read_value = MARF::get(&mut f, &next_block_header, &TriePath::from_bytes(&prev_path[..]).unwrap()).unwrap().unwrap();
                    assert_eq!(read_value.reserved.to_vec(), [j as u8; 40].to_vec());
                    assert_eq!(f.tell(), prev_block_header);
                }

                f.open(&next_block_header, false).unwrap();

                test_debug!("----------------");
                test_debug!("MARF verify cow");
                test_debug!("----------------");

                let c = marf_verify_cow(&mut f, &next_block_header, &next_path);
                let mut leaf_count = 0;
                for node in c.nodes.iter() {
                    let ptrs = match node {
                        TrieNodeType::Node4(ref data) => data.ptrs.to_vec(),
                        TrieNodeType::Node16(ref data) => data.ptrs.to_vec(),
                        TrieNodeType::Node48(ref data) => data.ptrs.to_vec(),
                        TrieNodeType::Node256(ref data) => data.ptrs.to_vec(),
                        TrieNodeType::Leaf(_) => vec![],
                    };
                    for ptr in ptrs {
                        if ptr.id() == TrieNodeID::Leaf {
                            leaf_count += 1;
                        }
                    }
                }

                dump_trie(&mut f);

                // only one leaf in this trie
                assert_eq!(leaf_count, 1);
                
                merkle_test_marf(&mut f, &next_block_header, &next_path, &[i as u8; 40].to_vec());
            }

            // all leaves are reachable from the last block 
            let last_block_header = BlockHeaderHash::from_bytes(&[18u8; 32]).unwrap();
            for i in 1..19 {
                // add a leaf at the end of the path
                let mut next_path = path.clone();
                next_path[19-i] = 20;
                
                let triepath = TriePath::from_bytes(&next_path[..]).unwrap();
                let value = TrieLeaf::new(&next_path[19-i+1..].to_vec(), &[i as u8; 40].to_vec());

                assert_eq!(MARF::get(&mut f, &last_block_header, &triepath).unwrap(), Some(value));
                
                merkle_test_marf(&mut f, &last_block_header, &next_path, &[i as u8; 40].to_vec());
            }
        }
    }

    // insert a range of 4096 consecutive keys (forcing node promotions) by varying the low-order bits.
    // every 128 keys, make a new trie
    #[test]
    fn marf_insert_4096_128_seq_low() {
        let path = "/tmp/rust_marf_insert_4096_128_seq_low".to_string();
        match fs::metadata(&path) {
            Ok(_) => {
                fs::remove_dir_all(&path).unwrap();
            },
            Err(_) => {}
        };
        let mut f = TrieFileStorage::new(&path).unwrap();

        let mut block_header = BlockHeaderHash::from_bytes(&[0u8; 32]).unwrap();
        MARF::format(&mut f, &block_header).unwrap();

        for i in 0..4096 {
            let i0 = i / 256;
            let i1 = i % 256;
            let path = [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,i0 as u8, i1 as u8];

            let triepath = TriePath::from_bytes(&path[..]).unwrap(); 
            let value = TrieLeaf::new(&vec![], &[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,i0 as u8, i1 as u8].to_vec());

            if (i + 1) % 128 == 0 {
                // next block 
                block_header = BlockHeaderHash::from_bytes(&[((i + 1) / 128) as u8; 32]).unwrap();
            }

            MARF::insert(&mut f, &block_header, &triepath, &value).unwrap();
             
            let read_value = MARF::get(&mut f, &block_header, &TriePath::from_bytes(&path[..]).unwrap()).unwrap().unwrap();
            assert_eq!(read_value.reserved.to_vec(), value.reserved.to_vec());
            assert_eq!(f.tell(), block_header);
        }

        for i in 0..4096 {
            // can read them all back
            let i0 = i / 256;
            let i1 = i % 256;
            let path = [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,i0 as u8, i1 as u8];

            let triepath = TriePath::from_bytes(&path[..]).unwrap(); 
            let value = TrieLeaf::new(&vec![], &[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,i0 as u8, i1 as u8].to_vec());

            let read_value = MARF::get(&mut f, &block_header, &TriePath::from_bytes(&path[..]).unwrap()).unwrap().unwrap();
            assert_eq!(read_value.reserved.to_vec(), value.reserved.to_vec());
            
            // can make a merkle proof to each one
            merkle_test_marf(&mut f, &block_header, &path.to_vec(), &value.reserved.to_vec());
        }
    }

    // insert a range of 4096 consecutive keys (forcing node promotions) by varying the high-order bits.
    // every 128 keys, make a new trie
    #[test]
    fn marf_insert_4096_128_seq_high() {
        let path = "/tmp/rust_marf_insert_4096_128_seq_high".to_string();
        match fs::metadata(&path) {
            Ok(_) => {
                fs::remove_dir_all(&path).unwrap();
            },
            Err(_) => {}
        };
        let mut f = TrieFileStorage::new(&path).unwrap();

        let mut block_header = BlockHeaderHash::from_bytes(&[0u8; 32]).unwrap();
        MARF::format(&mut f, &block_header).unwrap();

        for i in 0..4096 {
            let i0 = i / 256;
            let i1 = i % 256;
            let path = [i0 as u8, i1 as u8, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19];

            let triepath = TriePath::from_bytes(&path[..]).unwrap(); 
            let value = TrieLeaf::new(&vec![], &[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,i0 as u8, i1 as u8].to_vec());

            if (i + 1) % 128 == 0 {
                // next block 
                block_header = BlockHeaderHash::from_bytes(&[((i + 1) / 128) as u8; 32]).unwrap();
            }

            MARF::insert(&mut f, &block_header, &triepath, &value).unwrap();
             
            let read_value = MARF::get(&mut f, &block_header, &TriePath::from_bytes(&path[..]).unwrap()).unwrap().unwrap();
            assert_eq!(read_value.reserved.to_vec(), value.reserved.to_vec());
            assert_eq!(f.tell(), block_header);
        }

        for i in 0..4096 {
            // can read them all back
            let i0 = i / 256;
            let i1 = i % 256;
            let path = [i0 as u8, i1 as u8, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19];

            let triepath = TriePath::from_bytes(&path[..]).unwrap(); 
            let value = TrieLeaf::new(&vec![], &[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,i0 as u8, i1 as u8].to_vec());

            let read_value = MARF::get(&mut f, &block_header, &TriePath::from_bytes(&path[..]).unwrap()).unwrap().unwrap();
            assert_eq!(read_value.reserved.to_vec(), value.reserved.to_vec());
            
            // can make a merkle proof to each one
            merkle_test_marf(&mut f, &block_header, &path.to_vec(), &value.reserved.to_vec());
        }
    }

    // insert a leaf, open a new block, and attempt to split the leaf
    // TODO: try also when the leaf to split dangles from an intermediate node, not off of the root
    // (since we have a different backptr copy routine there)
    #[test]
    fn marf_split_leaf_path() {
        let path = "/tmp/rust_marf_insert_4096_128_seq_high".to_string();
        match fs::metadata(&path) {
            Ok(_) => {
                fs::remove_dir_all(&path).unwrap();
            },
            Err(_) => {}
        };
        let mut f = TrieFileStorage::new(&path).unwrap();

        let block_header = BlockHeaderHash::from_bytes(&[0u8; 32]).unwrap();
        MARF::format(&mut f, &block_header).unwrap();

        let path = [0u8; 20];
        let triepath = TriePath::from_bytes(&path[..]).unwrap(); 
        let value = TrieLeaf::new(&vec![], &[0u8; 40].to_vec());

        test_debug!("----------------");
        test_debug!("insert ({:?}, {:?}) in {:?}", &triepath, &value, &block_header);
        test_debug!("----------------");

        MARF::insert(&mut f, &block_header, &triepath, &value).unwrap();

        // insert a leaf along the same path but in a different block
        let block_header_2 = BlockHeaderHash::from_bytes(&[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1]).unwrap();
        let path_2 = [0,0,0,0,0,0,0,0,1,1,1,1,1,1,1,1,1,1,1,1];
        let triepath_2 = TriePath::from_bytes(&path_2[..]).unwrap(); 
        let value_2 = TrieLeaf::new(&vec![], &[1u8; 40].to_vec());
    
        test_debug!("----------------");
        test_debug!("insert ({:?}, {:?}) in {:?}", &triepath_2, &value_2, &block_header_2);
        test_debug!("----------------");

        MARF::insert(&mut f, &block_header_2, &triepath_2, &value_2).unwrap();

        test_debug!("----------------");
        test_debug!("get ({:?}, {:?}) in {:?}", &triepath, &value, &block_header_2);
        test_debug!("----------------");

        let read_value = MARF::get(&mut f, &block_header_2, &triepath).unwrap().unwrap();
        assert_eq!(read_value.reserved.to_vec(), value.reserved.to_vec());
        
        test_debug!("----------------");
        test_debug!("get ({:?}, {:?}) in {:?}", &triepath_2, &value_2, &block_header_2);
        test_debug!("----------------");

        let read_value_2 = MARF::get(&mut f, &block_header_2, &triepath_2).unwrap().unwrap();
        assert_eq!(read_value_2.reserved.to_vec(), value_2.reserved.to_vec());
    }

    
    // insert a random sequence of 65536 keys.  Every 2048 inserts, fork.
    #[test]
    fn marf_insert_random_65536_2048() {
        let path = "/tmp/rust_marf_insert_random_65536_2048".to_string();
        match fs::metadata(&path) {
            Ok(_) => {
                fs::remove_dir_all(&path).unwrap();
            },
            Err(_) => {}
        };
        let mut f = TrieFileStorage::new(&path).unwrap();

        let mut block_header = BlockHeaderHash([0u8; 32]);
        MARF::format(&mut f, &block_header).unwrap();
        
        let mut seed = TrieHash::from_data(&[]).as_bytes().to_vec();
        let mut start_time = get_epoch_time_ms();
        for i in 0..65536 {
            let i0 = i / 256;
            let i1 = i % 256;
            
            let path = TrieHash::from_data(&seed[..]).as_bytes()[0..20].to_vec();
            seed = path.clone();

            let triepath = TriePath::from_bytes(&path[..]).unwrap(); 
            let value = TrieLeaf::new(&vec![], &[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,i0 as u8, i1 as u8].to_vec());

            if (i + 1) % 2048 == 0 {
                // next block
                println!("next block!");
                block_header = BlockHeaderHash::from_bytes(&[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,((i+1)/2048) as u8,((i+1)%2048) as u8]).unwrap();
            }

            MARF::insert(&mut f, &block_header, &triepath, &value).unwrap();

            let read_value = MARF::get(&mut f, &block_header, &TriePath::from_bytes(&path[..]).unwrap()).unwrap().unwrap();
            assert_eq!(read_value.reserved.to_vec(), value.reserved.to_vec());
            assert_eq!(f.tell(), block_header);

            if i % 128 == 0 {
                let end_time = get_epoch_time_ms();
                let (read_count, write_count) = f.stats();
                let (node_reads, backptr_reads, node_writes, backptr_writes) = f.node_stats();
                let (leaf_reads, leaf_writes) = f.leaf_stats();
                println!("inserted {} in {} (1 insert = {} ms).  Read = {}, Write = {}, Node Reads = {}, Node Writes = {}, Backptr Reads = {}, BackPtr Writes = {}, Leaf Reads = {}, Leaf Writes = {}",
                         i, end_time - start_time, ((end_time - start_time) as f64) / 128.0, read_count, write_count, node_reads, node_writes, backptr_reads, backptr_writes, leaf_reads, leaf_writes);

                start_time = get_epoch_time_ms();
            }
        }
        
        let mut seed = TrieHash::from_data(&[]).as_bytes().to_vec();

        start_time = get_epoch_time_ms();
        for i in 0..65536 {
            // can read them all back
            let i0 = i / 256;
            let i1 = i % 256;
            
            let path = TrieHash::from_data(&seed[..]).as_bytes()[0..20].to_vec();
            seed = path.clone();

            let triepath = TriePath::from_bytes(&path[..]).unwrap(); 
            let value = TrieLeaf::new(&vec![], &[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,i0 as u8, i1 as u8].to_vec());

            let read_value = MARF::get(&mut f, &block_header, &TriePath::from_bytes(&path[..]).unwrap()).unwrap().unwrap();
            assert_eq!(read_value.reserved.to_vec(), value.reserved.to_vec());
            
            // can make a merkle proof to each one
            // merkle_test_marf(&mut f, &block_header, &path.to_vec(), &value.reserved.to_vec());
            if i % 128 == 0 {
                let end_time = get_epoch_time_ms();
                let (read_count, write_count) = f.stats();
                let (node_reads, backptr_reads, node_writes, backptr_writes) = f.node_stats();
                let (leaf_reads, leaf_writes) = f.leaf_stats();
                println!("Got {} in {} (1 get = {} ms).  Read = {}, Write = {}, Node Reads = {}, Node Writes = {}, Backptr Reads = {}, BackPtr Writes = {}, Leaf Reads = {}, Leaf Writes = {}",
                         i, end_time - start_time, ((end_time - start_time) as f64) / 128.0, read_count, write_count, node_reads, node_writes, backptr_reads, backptr_writes, leaf_reads, leaf_writes);
                
                start_time = get_epoch_time_ms();
            }
        }
    }
    
    // insert a random sequence of 1024 * 1024 keys.  Every 4096 inserts, fork.
    // Use file storage
    #[test]
    fn marf_insert_random_1048576_4096_file_storage() {
        let path = "/tmp/rust_marf_insert_random_1048576_4096".to_string();
        match fs::metadata(&path) {
            Ok(_) => {
                fs::remove_dir_all(&path).unwrap();
            },
            Err(_) => {}
        };
        let mut f = TrieFileStorage::new(&path).unwrap();

        let mut block_header = BlockHeaderHash::from_bytes(&[0u8; 32]).unwrap();
        MARF::format(&mut f, &block_header).unwrap();
        
        let mut seed = TrieHash::from_data(&[]).as_bytes().to_vec();
        let mut start_time = get_epoch_time_ms();
        let mut end_time = 0;
        let mut block_start_time = start_time;
        let mut prev_block_header = block_header.clone();

        for i in 0..1048576 {
            let i0 = (i & 0xff0000) >> 12;
            let i1 = (i & 0x00ff00) >> 8;
            let i2 = i & 0x0000ff;
            
            let path = TrieHash::from_data(&seed[..]).as_bytes()[0..20].to_vec();
            seed = path.clone();

            let triepath = TriePath::from_bytes(&path[..]).unwrap(); 
            let value = TrieLeaf::new(&vec![], &[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,i0 as u8, i1 as u8, i2 as u8].to_vec());

            if (i + 1) % 4096 == 0 {
                // next block
                end_time = get_epoch_time_ms();

                let flush_start_time = get_epoch_time_ms();
                f.flush().unwrap();
                let flush_end_time = get_epoch_time_ms();

                println!("next block! Processed 4096 keys in {} ms (flush = {} ms)", end_time - block_start_time, flush_end_time - flush_start_time);

                block_header = BlockHeaderHash::from_bytes(&[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,i0 as u8, i1 as u8, i2 as u8]).unwrap();
                block_start_time = get_epoch_time_ms();
            }

            MARF::insert(&mut f, &block_header, &triepath, &value).unwrap();

            if i % 128 == 0 {
                if block_header == prev_block_header {
                    end_time = get_epoch_time_ms();
                }
                else {
                    prev_block_header = block_header.clone();
                }
                let (read_count, write_count) = f.stats();
                let (node_reads, backptr_reads, node_writes, backptr_writes) = f.node_stats();
                let (leaf_reads, leaf_writes) = f.leaf_stats();
                println!("inserted {} in {} (1 insert = {} ms).  Read = {}, Write = {}, Node Reads = {}, Node Writes = {}, Backptr Reads = {}, BackPtr Writes = {}, Leaf Reads = {}, Leaf Writes = {}",
                         i, end_time - start_time, ((end_time - start_time) as f64) / 128.0, read_count, write_count, node_reads, node_writes, backptr_reads, backptr_writes, leaf_reads, leaf_writes);

                start_time = get_epoch_time_ms();
            }
        }
        
        f.flush().unwrap();
        
        let mut seed = TrieHash::from_data(&[]).as_bytes().to_vec();
        start_time = get_epoch_time_ms();
        for i in 0..1048576 {
            // can read them all back
            let i0 = (i & 0xff0000) >> 12;
            let i1 = (i & 0x00ff00) >> 8;
            let i2 = i & 0x0000ff;
            
            let path = TrieHash::from_data(&seed[..]).as_bytes()[0..20].to_vec();
            seed = path.clone();

            let triepath = TriePath::from_bytes(&path[..]).unwrap(); 
            let value = TrieLeaf::new(&vec![], &[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,i0 as u8, i1 as u8, i2 as u8].to_vec());

            let read_value = MARF::get(&mut f, &block_header, &TriePath::from_bytes(&path[..]).unwrap()).unwrap().unwrap();
            assert_eq!(read_value.reserved.to_vec(), value.reserved.to_vec());
            
            // can make a merkle proof to each one
            // merkle_test_marf(&mut f, &block_header, &path.to_vec(), &value.reserved.to_vec());
            if i % 128 == 0 {
                let end_time = get_epoch_time_ms();
                let (read_count, write_count) = f.stats();
                let (node_reads, backptr_reads, node_writes, backptr_writes) = f.node_stats();
                let (leaf_reads, leaf_writes) = f.leaf_stats();
                println!("Got {} in {} (1 get = {} ms).  Read = {}, Write = {}, Node Reads = {}, Node Writes = {}, Backptr Reads = {}, BackPtr Writes = {}, Leaf Reads = {}, Leaf Writes = {}",
                         i, end_time - start_time, ((end_time - start_time) as f64) / 128.0, read_count, write_count, node_reads, node_writes, backptr_reads, backptr_writes, leaf_reads, leaf_writes);
                
                start_time = get_epoch_time_ms();
            }
        }
    }
    
    #[test]
    fn marf_read_random_1048576_4096_file_storage() {
        let path = "/tmp/rust_marf_insert_random_1048576_4096".to_string();
        match fs::metadata(&path) {
            Err(_) => {
                println!("Run the marf_insert_random_1048576_4096 test first");
                return;
            },
            Ok(_) => {}
        };
        let mut f = TrieFileStorage::new(&path).unwrap();

        let block_header = BlockHeaderHash::from_bytes(&[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0xf0,0xff,0xff]).unwrap();
        f.open(&block_header, false).unwrap();

        let mut seed = TrieHash::from_data(&[]).as_bytes().to_vec();
        let mut start_time = 0;

        start_time = get_epoch_time_ms();
        for i in 0..1048576 {
            // can read them all back
            let i0 = (i & 0xff0000) >> 12;
            let i1 = (i & 0x00ff00) >> 8;
            let i2 = i & 0x0000ff;
            
            let path = TrieHash::from_data(&seed[..]).as_bytes()[0..20].to_vec();
            seed = path.clone();

            let triepath = TriePath::from_bytes(&path[..]).unwrap(); 
            let value = TrieLeaf::new(&vec![], &[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,i0 as u8, i1 as u8, i2 as u8].to_vec());

            let read_value = MARF::get(&mut f, &block_header, &TriePath::from_bytes(&path[..]).unwrap()).unwrap().unwrap();
            assert_eq!(read_value.reserved.to_vec(), value.reserved.to_vec());
            
            // can make a merkle proof to each one
            // merkle_test_marf(&mut f, &block_header, &path.to_vec(), &value.reserved.to_vec());
            if i % 128 == 0 {
                let end_time = get_epoch_time_ms();
                let (read_count, write_count) = f.stats();
                let (node_reads, backptr_reads, node_writes, backptr_writes) = f.node_stats();
                let (leaf_reads, leaf_writes) = f.leaf_stats();
                println!("Got {} in {} (1 get = {} ms).  Read = {}, Write = {}, Node Reads = {}, Node Writes = {}, Backptr Reads = {}, BackPtr Writes = {}, Leaf Reads = {}, Leaf Writes = {}",
                         i, end_time - start_time, ((end_time - start_time) as f64) / 128.0, read_count, write_count, node_reads, node_writes, backptr_reads, backptr_writes, leaf_reads, leaf_writes);
                
                start_time = get_epoch_time_ms();
            }
        }
    }
    
    // insert a range of 4096 consecutive keys (forcing node promotions) by varying the low-order bits.
    // every 128 keys, make a new trie.
    // Use the TrieFileStorage backend
    #[test]
    fn marf_insert_128_32_file_storage() {
        let path = "/tmp/rust_marf_insert_128_32_file_storage".to_string();
        match fs::metadata(&path) {
            Ok(_) => {
                fs::remove_dir_all(&path).unwrap();
            },
            Err(_) => {}
        };

        let mut f = TrieFileStorage::new(&path).unwrap();

        let mut block_header = BlockHeaderHash::from_bytes(&[0u8; 32]).unwrap();
        MARF::format(&mut f, &block_header).unwrap();

        for i in 0..128 {
            let i0 = i / 256;
            let i1 = i % 256;
            let path = [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,i0 as u8, i1 as u8];

            let triepath = TriePath::from_bytes(&path[..]).unwrap(); 
            let value = TrieLeaf::new(&vec![], &[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,i0 as u8, i1 as u8].to_vec());

            if (i + 1) % 32 == 0 {
                // next block
                block_header = BlockHeaderHash::from_bytes(&[((i + 1) / 32) as u8; 32]).unwrap();
                test_debug!("block header is now {:?}", &block_header);
                f.flush().unwrap();
            }

            test_debug!("insert {}", i);
            MARF::insert(&mut f, &block_header, &triepath, &value).unwrap();
             
            test_debug!("get {}", i);
            let read_value = MARF::get(&mut f, &block_header, &TriePath::from_bytes(&path[..]).unwrap()).unwrap().unwrap();
            assert_eq!(read_value.reserved.to_vec(), value.reserved.to_vec());
            assert_eq!(f.tell(), block_header);
            
            // can make a merkle proof to each one
            merkle_test_marf(&mut f, &block_header, &path.to_vec(), &value.reserved.to_vec());
        }
        
        f.flush().unwrap();

        f.open(&block_header, false).unwrap();
        dump_trie(&mut f);

        test_debug!("------------");
        test_debug!("get all and get merkle proofs");
        test_debug!("------------");

        for i in 0..128 {
            // can read them all back
            let i0 = i / 256;
            let i1 = i % 256;
            let path = [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,i0 as u8, i1 as u8];

            let triepath = TriePath::from_bytes(&path[..]).unwrap(); 
            let value = TrieLeaf::new(&vec![], &[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,i0 as u8, i1 as u8].to_vec());

            let read_value = MARF::get(&mut f, &block_header, &TriePath::from_bytes(&path[..]).unwrap()).unwrap().unwrap();
            assert_eq!(read_value.reserved.to_vec(), value.reserved.to_vec());
            
            // can make a merkle proof to each one
            merkle_test_marf(&mut f, &block_header, &path.to_vec(), &value.reserved.to_vec());
        }

        for i in 0..(128/32) {
            let block_header = BlockHeaderHash::from_bytes(&[i as u8; 32]).unwrap();
            f.open(&block_header, false).unwrap();
            dump_trie(&mut f);
        }
    }

    // insert a range of 4096 consecutive keys (forcing node promotions) by varying the low-order bits.
    // every 128 keys, make a new trie.
    // Use the TrieFileStorage backend
    #[test]
    fn marf_insert_4096_128_file_storage() {
        let path = "/tmp/rust_marf_insert_4096_128_file_storage".to_string();
        match fs::metadata(&path) {
            Ok(_) => {
                fs::remove_dir_all(&path).unwrap();
            },
            Err(_) => {}
        };

        let mut f = TrieFileStorage::new(&path).unwrap();

        let mut block_header = BlockHeaderHash::from_bytes(&[0u8; 32]).unwrap();
        MARF::format(&mut f, &block_header).unwrap();

        for i in 0..4096 {
            let i0 = i / 256;
            let i1 = i % 256;
            let path = [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,i0 as u8, i1 as u8];

            let triepath = TriePath::from_bytes(&path[..]).unwrap(); 
            let value = TrieLeaf::new(&vec![], &[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,i0 as u8, i1 as u8].to_vec());

            if (i + 1) % 128 == 0 {
                // next block
                block_header = BlockHeaderHash::from_bytes(&[((i + 1) / 128) as u8; 32]).unwrap();
                test_debug!("block header is now {:?}", &block_header);
                f.flush().unwrap();
            }

            test_debug!("insert {}", i);
            MARF::insert(&mut f, &block_header, &triepath, &value).unwrap();
             
            test_debug!("get {}", i);
            let read_value = MARF::get(&mut f, &block_header, &TriePath::from_bytes(&path[..]).unwrap()).unwrap().unwrap();
            assert_eq!(read_value.reserved.to_vec(), value.reserved.to_vec());
            assert_eq!(f.tell(), block_header);
            
            // can make a merkle proof to each one
            merkle_test_marf(&mut f, &block_header, &path.to_vec(), &value.reserved.to_vec());
        }
        
        f.flush().unwrap();

        test_debug!("------------");
        test_debug!("get all and get merkle proofs");
        test_debug!("------------");

        for i in 0..4096 {
            // can read them all back
            let i0 = i / 256;
            let i1 = i % 256;
            let path = [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,i0 as u8, i1 as u8];

            let triepath = TriePath::from_bytes(&path[..]).unwrap(); 
            let value = TrieLeaf::new(&vec![], &[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,i0 as u8, i1 as u8].to_vec());

            let read_value = MARF::get(&mut f, &block_header, &TriePath::from_bytes(&path[..]).unwrap()).unwrap().unwrap();
            assert_eq!(read_value.reserved.to_vec(), value.reserved.to_vec());
            
            // can make a merkle proof to each one
            merkle_test_marf(&mut f, &block_header, &path.to_vec(), &value.reserved.to_vec());
        }

        for i in 0..(4096/128) {
            let block_header = BlockHeaderHash::from_bytes(&[i as u8; 32]).unwrap();
            f.open(&block_header, false).unwrap();
            dump_trie(&mut f);
        }
    }
}
