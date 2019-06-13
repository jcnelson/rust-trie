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

// print debug statements while testing
#[allow(unused_macros)]
macro_rules! test_debug {
    ($($arg:tt)*) => ({
        use std::env;
        if env::var("BLOCKSTACK_DEBUG") == Ok("1".to_string()) {
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

pub struct TrieHash(pub [u8; 32]);
impl_array_newtype!(TrieHash, u8, 32);
impl_array_hexstring_fmt!(TrieHash);
impl_byte_array_newtype!(TrieHash, u8, 32);

impl TrieHash {
    pub fn from_data(data: &[u8]) -> TrieHash {
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
    ExistsError,
    BadSeekValue,
    BackPtrError,
    CorruptionError,
    InvalidNodeError,
    LeafError,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Error::IOError(ref e) => fmt::Display::fmt(e, f),
            Error::NotFoundError => f.write_str(error::Error::description(self)),
            Error::ExistsError => f.write_str(error::Error::description(self)),
            Error::BadSeekValue => f.write_str(error::Error::description(self)),
            Error::BackPtrError => f.write_str(error::Error::description(self)),
            Error::CorruptionError => f.write_str(error::Error::description(self)),
            Error::InvalidNodeError => f.write_str(error::Error::description(self)),
            Error::LeafError => f.write_str(error::Error::description(self)),
        }
    }
}

impl error::Error for Error {
    fn cause(&self) -> Option<&error::Error> {
        match *self {
            Error::IOError(ref e) => Some(e),
            Error::NotFoundError => None,
            Error::ExistsError => None,
            Error::BadSeekValue => None,
            Error::BackPtrError => None,
            Error::CorruptionError => None,
            Error::InvalidNodeError => None,
            Error::LeafError => None,
        }
    }

    fn description(&self) -> &str {
        match *self {
            Error::IOError(ref e) => e.description(),
            Error::NotFoundError => "Object not found",
            Error::ExistsError => "Object exists",
            Error::BadSeekValue => "Bad seek value",
            Error::BackPtrError => "Encountered a back-pointer",
            Error::CorruptionError => "Trie data is corrupted",
            Error::InvalidNodeError => "Encountered an unexpected node",
            Error::LeafError => "Encountered an unexpected leaf",
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
    pub const BackPtr : u8 = 1;
    pub const Leaf: u8 = 5;
    pub const Node4 : u8 = 3;
    pub const Node16 : u8 = 15;
    pub const Node48 : u8 = 47;
    pub const Node256 : u8 = 255;
}

pub struct TriePath([u8; 20]);
impl_array_newtype!(TriePath, u8, 20);
impl_array_hexstring_fmt!(TriePath);
impl_byte_array_newtype!(TriePath, u8, 20);

pub trait TrieNode {
    fn id(&self) -> u8;
    fn empty() -> Self;
    fn walk(&self, chr: u8) -> Option<TriePtr>;
    fn insert(&mut self, ptr: &TriePtr) -> bool;
    fn replace(&mut self, ptr: &TriePtr) -> bool;
    fn from_bytes<R: Read>(r: &mut R) -> Result<Self, Error>
        where Self: std::marker::Sized;
    fn to_bytes(&self) -> Vec<u8>;
    fn to_consensus_bytes(&self) -> Vec<u8>;
    fn ptrs(&self) -> &[TriePtr];

    // this is a way to construct a TrieNodeType from an object that implements this trait
    // DO NOT USE DIRECTLY
    fn try_as_node4(&self) -> Option<TrieNodeType>;
    fn try_as_node16(&self) -> Option<TrieNodeType>;
    fn try_as_node48(&self) -> Option<TrieNodeType>;
    fn try_as_node256(&self) -> Option<TrieNodeType>;
    fn try_as_leaf(&self) -> Option<TrieNodeType>;
    fn try_as_backptr(&self) -> Option<TrieNodeType>;
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct TriePtr {
    id: u8,
    chr: u8,
    ptr: u64
}

pub fn ptrs_fmt(ptrs: &[TriePtr]) -> String {
    let mut strs = vec![];
    for i in 0..ptrs.len() {
        if ptrs[i].id != TrieNodeID::Empty {
            strs.push(format!("id{}chr{:02x}ptr{}", ptrs[i].id, ptrs[i].chr, ptrs[i].ptr))
        }
    }
    strs.join(",")
}

pub const TRIEPTR_SIZE : usize = 10;

impl Default for TriePtr {
    fn default() -> TriePtr {
        TriePtr { id: 0, chr: 0, ptr: 0 }
    }
}

impl TriePtr {
    pub fn new(id: u8, chr: u8, ptr: u64) -> TriePtr {
        TriePtr {
            id: id,
            chr: chr,
            ptr: ptr
        }
    }

    pub fn empty(&self) -> bool {
        self.id == 0
    }

    pub fn id(&self) -> u8 {
        self.id
    }

    pub fn chr(&self) -> u8 {
        self.chr
    }

    pub fn ptr(&self) -> u64 {
        self.ptr
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        let mut ret = vec![];
        let ptr = self.ptr();

        let ptr_bytes = [
            ((ptr & 0xff00000000000000) >> 56) as u8,
            ((ptr & 0x00ff000000000000) >> 48) as u8,
            ((ptr & 0x0000ff0000000000) >> 40) as u8,
            ((ptr & 0x000000ff00000000) >> 32) as u8,
            ((ptr & 0x00000000ff000000) >> 24) as u8,
            ((ptr & 0x0000000000ff0000) >> 16) as u8,
            ((ptr & 0x000000000000ff00) >> 8) as u8,
            ((ptr & 0x00000000000000ff)) as u8
        ];

        ret.push(self.id());
        ret.push(self.chr());

        ret.push(ptr_bytes[0]);
        ret.push(ptr_bytes[1]);
        ret.push(ptr_bytes[2]);
        ret.push(ptr_bytes[3]);
        ret.push(ptr_bytes[4]);
        ret.push(ptr_bytes[5]);
        ret.push(ptr_bytes[6]);
        ret.push(ptr_bytes[7]);

        assert!(ret.len() == TRIEPTR_SIZE);
        ret
    }

    pub fn to_consensus_bytes(&self) -> Vec<u8> {
        // like to_bytes(), but without insertion-order
        let mut ret = vec![];
        ret.push(self.id());
        ret.push(self.chr());
        ret
    }

    pub fn from_bytes(bytes: &Vec<u8>) -> TriePtr {
        assert!(bytes.len() >= TRIEPTR_SIZE);
        let id = bytes[0];
        let chr = bytes[1];
        let ptr =
            (bytes[2] as u64) << 56 |
            (bytes[3] as u64) << 48 |
            (bytes[4] as u64) << 40 |
            (bytes[5] as u64) << 32 |
            (bytes[6] as u64) << 24 |
            (bytes[7] as u64) << 16 |
            (bytes[8] as u64) << 8 |
            (bytes[9] as u64);

        TriePtr {
            id: id,
            chr: chr,
            ptr: ptr
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
    block_hashes: Vec<BlockHeaderHash>  // (optional) list of Tries we've visited.  block_hashes[i] corresponds to node_ptrs[i]
}

impl TrieCursor {
    pub fn new(path: &TriePath) -> TrieCursor {
        TrieCursor {
            path: path.clone(),
            index: 0,
            node_path_index: 0,
            nodes: vec![],
            node_ptrs: vec![TriePtr::new(TrieNodeID::Node256, 0, 0)],
            block_hashes: vec![],
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
            // should not happen
            TrieNodeType::BackPtr(_) => panic!("cursor cannot process a backptr node")
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
            TrieNodeType::BackPtr(ref data) => {
                // can't walk this
                test_debug!("cursor: encountered backptr {:?}", data);
                return None;
            }
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
            let ptr_opt = match node {
                TrieNodeType::Node4(ref node4) => node4.walk(chr),
                TrieNodeType::Node16(ref node16) => node16.walk(chr),
                TrieNodeType::Node48(ref node48) => node48.walk(chr),
                TrieNodeType::Node256(ref node256) => node256.walk(chr),
                _ => None
            };
            match ptr_opt {
                Some(ref ptr) => {
                    self.node_ptrs.push(ptr.clone());
                    self.block_hashes.push(block_hash.clone());
                },
                None => {}
            }

            if ptr_opt.is_none() {
                test_debug!("cursor: not found: chr = {}, self.index = {}, self.path = {:?}", chr, self.index-1, &path_bytes);
            }
            ptr_opt
        }
        else {
            test_debug!("cursor: now out of path");
            None
        }
    }
}


#[derive(Clone)]
pub struct TrieLeaf {
    path: Vec<u8>,
    reserved: [u8; 40]
}

impl fmt::Debug for TrieLeaf {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "TrieLeaf(path={} reserved={})", &to_hex(&self.path), &to_hex(&self.reserved.to_vec()))
    }
}

impl PartialEq for TrieLeaf {
    fn eq(&self, other: &TrieLeaf) -> bool {
        self.path == other.path && slice_partialeq(&self.reserved, &other.reserved)
    }
}


impl TrieLeaf {
    pub fn new(path: &Vec<u8>, data: &Vec<u8>) -> TrieLeaf {
        assert!(data.len() <= 40);
        let mut bytes = [0u8; 40];
        bytes.copy_from_slice(&data[..]);
        TrieLeaf {
            path: path.clone(),
            reserved: bytes
        }
    }
}

#[derive(Clone, PartialEq)]
pub struct TrieNode4 {
    path: Vec<u8>,
    ptrs: [TriePtr; 4]
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
            ptrs: [TriePtr::default(); 4]
        }
    }
}

#[derive(Clone, PartialEq)]
pub struct TrieNode16 {
    path: Vec<u8>,
    ptrs: [TriePtr; 16]
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
            ptrs: [TriePtr::default(); 16]
        }
    }

    pub fn from_node4(node4: &TrieNode4) -> TrieNode16 {
        let mut ptrs = [TriePtr::default(); 16];
        for i in 0..4 {
            ptrs[i] = node4.ptrs[i].clone();
        }
        TrieNode16 {
            path: node4.path.clone(),
            ptrs: ptrs
        }
    }
}

#[derive(Clone)]
pub struct TrieNode48 {
    path: Vec<u8>,
    indexes: [i8; 256],
    ptrs: [TriePtr; 48]
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
            ptrs: [TriePtr::default(); 48]
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
            ptrs: ptrs
        }
    }
}

#[derive(Clone)]
pub struct TrieNode256 {
    path: Vec<u8>,
    ptrs: [TriePtr; 256]
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
            ptrs: [TriePtr::default(); 256]
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

/// Back-pointer to a TrieNode in a separate trie in the MARF
#[derive(Clone)]
pub struct TrieBackPtr {
    block_hash: BlockHeaderHash,
    ptr: TriePtr
}

impl fmt::Debug for TrieBackPtr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "TrieBackPtr(block_hash={}, ptr={})", &to_hex(self.block_hash.as_bytes()), ptrs_fmt(&[self.ptr]))
    }
}

impl PartialEq for TrieBackPtr {
    fn eq(&self, other: &TrieBackPtr) -> bool {
        self.block_hash == other.block_hash && self.ptr == other.ptr
    }
}

impl TrieBackPtr {
    pub fn new(block_hash: &BlockHeaderHash, ptr: &TriePtr) -> TrieBackPtr {
        TrieBackPtr {
            block_hash: block_hash.clone(),
            ptr: ptr.clone()
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

fn path_to_bytes(p: &Vec<u8>) -> Vec<u8> {
    // always true by construction
    assert!(p.len() < 256);
    let mut ret = Vec::with_capacity(p.len() + 1);
    ret.push(p.len() as u8);
    ret.append(&mut p.clone());
    ret
}

fn path_from_bytes<R: Read>(r: &mut R) -> Result<Vec<u8>, Error> {
    let mut lenbuf = [0u8; 1];
    let l_lenbuf = read_all(r, &mut lenbuf)?;

    if l_lenbuf != 1 {
        return Err(Error::CorruptionError);
    }

    let mut retbuf = vec![0; lenbuf[0] as usize];
    let l_retbuf = read_all(r, &mut retbuf)?;

    if l_retbuf != (lenbuf[0] as usize) {
        return Err(Error::CorruptionError);
    }
    
    Ok(retbuf)
}

fn check_node_id(node_id: u8) -> bool {
    node_id == TrieNodeID::Leaf ||
    node_id == TrieNodeID::BackPtr ||
    node_id == TrieNodeID::Node4 ||
    node_id == TrieNodeID::Node16 ||
    node_id == TrieNodeID::Node48 ||
    node_id == TrieNodeID::Node256
}

fn node_id_to_ptr_count(node_id: u8) -> usize {
    match node_id {
        TrieNodeID::Leaf => 0,
        TrieNodeID::BackPtr => 1,
        TrieNodeID::Node4 => 4,
        TrieNodeID::Node16 => 16,
        TrieNodeID::Node48 => 48,
        TrieNodeID::Node256 => 256,
        _ => panic!("Unknown node ID {}", node_id)
    }
}

fn ptrs_to_bytes(node_id: u8, ptrs: &[TriePtr]) -> Vec<u8> {
    assert!(check_node_id(node_id));
    assert_eq!(node_id_to_ptr_count(node_id), ptrs.len());

    let mut ret = vec![];
    ret.push(node_id);
    for ptr in ptrs.iter() {
        let mut buf = ptr.to_bytes();
        ret.append(&mut buf);
    }
    ret
}

fn ptrs_to_consensus_bytes(node_id: u8, ptrs: &[TriePtr]) -> Vec<u8> {
    assert!(check_node_id(node_id));
    let mut ret = vec![];
    ret.push(node_id);
    for ptr in ptrs.iter() {
        let mut buf = ptr.to_consensus_bytes();
        ret.append(&mut buf);
    }
    ret
}

fn ptrs_from_bytes<R: Read>(node_id: u8, r: &mut R) -> Result<Vec<TriePtr>, Error> {
    if !check_node_id(node_id) {
        test_debug!("Bad node ID {}", node_id);
        return Err(Error::CorruptionError);
    }

    let mut idbuf = [0u8; 1];
    let l_idbuf = read_all(r, &mut idbuf)?;

    if l_idbuf != 1 {
        test_debug!("Bad l_idbuf: {}", l_idbuf);
        return Err(Error::CorruptionError);
    }
    if idbuf[0] != node_id {
        test_debug!("Bad idbuf: {} != {}", idbuf[0], node_id);
        return Err(Error::CorruptionError);
    }

    let num_ptrs = node_id_to_ptr_count(node_id);
    let mut bytes = vec![0; num_ptrs * TRIEPTR_SIZE];
    let l_bytes = read_all(r, &mut bytes)?;

    if l_bytes != num_ptrs * TRIEPTR_SIZE {
        test_debug!("Bad l_bytes: {} != {}", l_bytes, num_ptrs * TRIEPTR_SIZE);
        return Err(Error::CorruptionError);
    }
    
    let mut ret = Vec::with_capacity(num_ptrs);
    for i in 0..num_ptrs {
        let ptr_bytes = &bytes[i*TRIEPTR_SIZE..(i+1)*TRIEPTR_SIZE];
        let ptr = TriePtr::from_bytes(&ptr_bytes.to_vec());
        ret.push(ptr);
    }
    Ok(ret)
}

impl TrieNode for TrieNode4 {
    fn id(&self) -> u8 {
        TrieNodeID::Node4
    }

    fn empty() -> TrieNode4 {
        TrieNode4 {
            path: vec![],
            ptrs: [TriePtr::default(); 4]
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

    fn to_bytes(&self) -> Vec<u8> {
        let mut ret = ptrs_to_bytes(TrieNodeID::Node4, &self.ptrs);
        ret.append(&mut path_to_bytes(&self.path));
        ret
    }

    fn to_consensus_bytes(&self) -> Vec<u8> {
        let mut ret = ptrs_to_consensus_bytes(TrieNodeID::Node4, &self.ptrs);
        ret.append(&mut path_to_bytes(&self.path));
        ret
    }

    fn from_bytes<R: Read>(r: &mut R) -> Result<TrieNode4, Error> {
        let ptrs = ptrs_from_bytes(TrieNodeID::Node4, r)?;
        assert!(ptrs.len() == 4);

        let path = path_from_bytes(r)?;

        let mut ptrs_slice = [TriePtr::default(); 4];
        ptrs_slice.copy_from_slice(&ptrs[..]);

        Ok(TrieNode4 {
            path,
            ptrs: ptrs_slice
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
    fn try_as_backptr(&self) -> Option<TrieNodeType> { None }
}

impl TrieNode for TrieNode16 {
    fn id(&self) -> u8 {
        TrieNodeID::Node16
    }

    fn empty() -> TrieNode16 {
        TrieNode16 {
            path: vec![],
            ptrs: [TriePtr::default(); 16]
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

    fn to_bytes(&self) -> Vec<u8> {
        let mut ret = ptrs_to_bytes(TrieNodeID::Node16, &self.ptrs);
        ret.append(&mut path_to_bytes(&self.path));
        ret
    }

    fn to_consensus_bytes(&self) -> Vec<u8> {
        let mut ret = ptrs_to_consensus_bytes(TrieNodeID::Node16, &self.ptrs);
        ret.append(&mut path_to_bytes(&self.path));
        ret
    }

    fn from_bytes<R: Read>(r: &mut R) -> Result<TrieNode16, Error> {
        let ptrs = ptrs_from_bytes(TrieNodeID::Node16, r)?;
        assert!(ptrs.len() == 16);

        let mut ptrs_slice = [TriePtr::default(); 16];
        ptrs_slice.copy_from_slice(&ptrs[..]);

        let path = path_from_bytes(r)?;
        Ok(TrieNode16 {
            path, 
            ptrs: ptrs_slice
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
    fn try_as_backptr(&self) -> Option<TrieNodeType> { None }
}

impl TrieNode for TrieNode48 {
    fn id(&self) -> u8 {
        TrieNodeID::Node48
    }

    fn empty() -> TrieNode48 {
        TrieNode48 {
            path: vec![],
            indexes: [-1; 256],
            ptrs: [TriePtr::default(); 48]
        }
    }

    fn walk(&self, chr: u8) -> Option<TriePtr> {
        let idx = self.indexes[chr as usize];
        if idx >= 0 && idx < 48 && self.ptrs[idx as usize].id() != TrieNodeID::Empty {
            return Some(self.ptrs[idx as usize].clone());
        }
        return None;
    }

    fn to_bytes(&self) -> Vec<u8> {
        let mut ret = ptrs_to_bytes(TrieNodeID::Node48, &self.ptrs);
        ret.append(&mut self.indexes.iter().map(|i| { let j = *i as u8; j } ).collect());
        ret.append(&mut path_to_bytes(&self.path));
        ret
    }
    
    fn to_consensus_bytes(&self) -> Vec<u8> {
        let mut ret = ptrs_to_consensus_bytes(TrieNodeID::Node48, &self.ptrs);
        ret.append(&mut self.indexes.iter().map(|i| { let j = *i as u8; j } ).collect());
        ret.append(&mut path_to_bytes(&self.path));
        ret
    }

    fn from_bytes<R: Read>(r: &mut R) -> Result<TrieNode48, Error> {
        let ptrs = ptrs_from_bytes(TrieNodeID::Node48, r)?;
        assert!(ptrs.len() == 48);
        
        let mut indexes = [0u8; 256];
        let l_indexes = r.read(&mut indexes)
            .map_err(Error::IOError)?;
       
        if l_indexes != 256 {
            return Err(Error::CorruptionError);
        }

        let path = path_from_bytes(r)?;

        let mut ptrs_slice = [TriePtr::default(); 48];
        ptrs_slice.copy_from_slice(&ptrs[..]);

        let indexes_i8 : Vec<i8> = indexes.iter().map(|i| { let j = *i as i8; j } ).collect();
        let mut indexes_slice = [0i8; 256];
        indexes_slice.copy_from_slice(&indexes_i8[..]);

        for ptr in ptrs_slice.iter() {
            if !(ptr.id() == TrieNodeID::Empty || (indexes_slice[ptr.chr() as usize] >= 0 && indexes_slice[ptr.chr() as usize] < 48)) {
                return Err(Error::CorruptionError);
            }
        }
        for i in 0..256 {
            if !(indexes_slice[i] < 0 || (indexes_slice[i] >= 0 && (indexes_slice[i] as usize) < ptrs_slice.len() && ptrs_slice[indexes_slice[i] as usize].id() != TrieNodeID::Empty)) {
                return Err(Error::CorruptionError);
            }
        }

        Ok(TrieNode48 {
            path,
            indexes: indexes_slice,
            ptrs: ptrs_slice
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
    fn try_as_backptr(&self) -> Option<TrieNodeType> { None }
}

impl TrieNode for TrieNode256 {
    fn id(&self) -> u8 {
        TrieNodeID::Node256
    }

    fn empty() -> TrieNode256 {
        TrieNode256 {
            path: vec![],
            ptrs: [TriePtr::default(); 256]
        }
    }

    fn walk(&self, chr: u8) -> Option<TriePtr> {
        if self.ptrs[chr as usize].id() != TrieNodeID::Empty {
            return Some(self.ptrs[chr as usize].clone());
        }
        return None;
    }

    fn to_bytes(&self) -> Vec<u8> {
        let mut ret = ptrs_to_bytes(TrieNodeID::Node256, &self.ptrs);
        ret.append(&mut path_to_bytes(&self.path));
        ret
    }

    fn to_consensus_bytes(&self) -> Vec<u8> {
        let mut ret = ptrs_to_consensus_bytes(TrieNodeID::Node256, &self.ptrs);
        ret.append(&mut path_to_bytes(&self.path));
        ret
    }

    fn from_bytes<R: Read>(r: &mut R) -> Result<TrieNode256, Error> {
        let ptrs = ptrs_from_bytes(TrieNodeID::Node256, r)?;
        assert!(ptrs.len() == 256);

        let path = path_from_bytes(r)?;

        let mut ptrs_slice = [TriePtr::default(); 256];
        ptrs_slice.copy_from_slice(&ptrs[..]);

        Ok(TrieNode256 {
            path, 
            ptrs: ptrs_slice
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
    fn try_as_backptr(&self) -> Option<TrieNodeType> { None }
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

    fn to_bytes(&self) -> Vec<u8> {
        let mut ret = path_to_bytes(&self.path);
        ret.append(&mut self.reserved.to_vec());
        ret
    }

    fn to_consensus_bytes(&self) -> Vec<u8> {
        self.to_bytes()
    }

    fn from_bytes<R: Read>(r: &mut R) -> Result<TrieLeaf, Error> {
        let path = path_from_bytes(r)?;
        let mut reserved = [0u8; 40];
        let l_reserved = r.read(&mut reserved)
            .map_err(Error::IOError)?;

        if l_reserved != 40 {
            return Err(Error::CorruptionError);
        }
        
        Ok(TrieLeaf {
            path: path,
            reserved: reserved
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
    fn try_as_backptr(&self) -> Option<TrieNodeType> { None }
}

impl TrieNode for TrieBackPtr {
    fn id(&self) -> u8 {
        TrieNodeID::BackPtr
    }

    fn empty() -> TrieBackPtr {
        TrieBackPtr {
            block_hash: BlockHeaderHash([0u8; 32]),
            ptr: TriePtr::new(0,0,0)
        }
    }

    fn walk(&self, _chr: u8) -> Option<TriePtr> {
        // can't be walked directly
        None
    }

    fn to_bytes(&self) -> Vec<u8> {
        let mut ret = ptrs_to_bytes(TrieNodeID::BackPtr, &[self.ptr]);
        ret.append(&mut self.block_hash.as_bytes().to_vec());
        ret
    }

    fn to_consensus_bytes(&self) -> Vec<u8> {
        let mut ret = ptrs_to_consensus_bytes(TrieNodeID::BackPtr, &[self.ptr]);
        ret.append(&mut self.block_hash.as_bytes().to_vec());
        ret
    }

    fn from_bytes<R: Read>(r: &mut R) -> Result<TrieBackPtr, Error> {
        let ptrs = ptrs_from_bytes(TrieNodeID::BackPtr, r)?;
        assert!(ptrs.len() == 1);

        let mut block_hash_bytes = [0u8; 32];
        let l_block_hash = r.read(&mut block_hash_bytes)
            .map_err(Error::IOError)?;

        if l_block_hash != 32 {
            return Err(Error::CorruptionError);
        }

        Ok(TrieBackPtr {
            block_hash: BlockHeaderHash(block_hash_bytes),
            ptr: ptrs[0].clone()
        })
    }

    fn insert(&mut self, _ptr: &TriePtr) -> bool {
        panic!("can't insert into a backptr");
    }

    fn replace(&mut self, _ptr: &TriePtr) -> bool {
        panic!("can't replace in a backptr");
    }
    
    fn ptrs(&self) -> &[TriePtr] {
        &[]
    }
    
    fn try_as_node4(&self) -> Option<TrieNodeType> { None }
    fn try_as_node16(&self) -> Option<TrieNodeType> { None }
    fn try_as_node48(&self) -> Option<TrieNodeType> { None }
    fn try_as_node256(&self) -> Option<TrieNodeType> { None }
    fn try_as_leaf(&self) -> Option<TrieNodeType> { None }
    fn try_as_backptr(&self) -> Option<TrieNodeType> { Some(TrieNodeType::BackPtr(self.clone())) }
}

#[derive(Debug, Clone, PartialEq)]
pub enum TrieNodeType {
    Node4(TrieNode4),
    Node16(TrieNode16),
    Node48(TrieNode48),
    Node256(TrieNode256),
    Leaf(TrieLeaf),
    BackPtr(TrieBackPtr)
}

/// hash this node and its childrens' hashes
/// (put outside the trie since an S-type isn't needed)
fn get_node_hash<T: TrieNode + std::fmt::Debug>(node: &T, child_hashes: &Vec<TrieHash>) -> TrieHash {
    let mut sha2 = Sha512Trunc256::new();
    sha2.input(&node.to_consensus_bytes()[..]);
    for child_hash in child_hashes {
        sha2.input(&child_hash.as_bytes());
    }
    
    let mut res = [0u8; 32];
    res.copy_from_slice(sha2.result().as_slice());

    let ret = TrieHash(res);
    test_debug!("get_node_hash: hash {:?} = {:?} + {:?}", &ret, node, child_hashes);
    ret
}

fn _read_hash<F: Read + Write + Seek>(f: &mut F) -> Result<TrieHash, Error> {
    let mut hashbytes = [0u8; 32];
    f.read(&mut hashbytes)
        .map_err(Error::IOError)?;
    Ok(TrieHash(hashbytes))
}

fn read_node_hash<F: Read + Write + Seek>(f: &mut F, ptr: &TriePtr) -> Result<TrieHash, Error> {
    fseek(f, ptr.ptr())?;
    _read_hash(f)
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
    let h = read_node_hash(f, ptr)?;
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
        TrieNodeID::BackPtr => {
            let node = TrieBackPtr::from_bytes(f)?;
            TrieNodeType::BackPtr(node)
        },
        _ => {
            panic!("Unknown trie node type {}", ptr.id());
        }
    };

    Ok((node, h))
}

/// write all the bytes for a node, including its hash
fn write_node_bytes<F: Read + Write + Seek, T: TrieNode + std::fmt::Debug>(f: &mut F, node: &T, hash: TrieHash) -> Result<(), Error> {
    let mut cnt = 0;
    let mut bytes = hash.as_bytes().to_vec();
    let mut node_bytes = node.to_bytes();

    bytes.append(&mut node_bytes);

    let ptr = ftell(f)?;
    test_debug!("write_node: {:?} {:?} at {}-{}", node, &hash, ptr, ptr + bytes.len() as u64);

    while cnt < bytes.len() {
        let nw = f.write(&bytes[cnt..bytes.len()])
            .map_err(Error::IOError)?;
        cnt += nw;
    }
    
    Ok(())
}

pub trait TrieStorage {
    fn extend(&mut self, bhh: &BlockHeaderHash) -> Result<(), Error>;
    fn open(&mut self, bhh: &BlockHeaderHash) -> Result<(), Error>;
    fn tell(&self) -> BlockHeaderHash;
    fn format(&mut self) -> Result<(), Error>;
    fn format_block(&mut self, &BlockHeaderHash) -> Result<(), Error>;
    fn read_node_hash(&mut self, ptr: &TriePtr) -> Result<TrieHash, Error>;
    fn read_node(&mut self, ptr: &TriePtr) -> Result<(TrieNodeType, TrieHash), Error>;
    fn write_node(&mut self, node: &TrieNodeType, hash: TrieHash) -> Result<(), Error>;
}

/// This is about 30% faster than TrieIOBuffer for randomly-distributed keys
/// and about 20% faster than TrieIOBuffer for sequential keys.
/// TODO add a way to convert this into a TrieIOBuffer
pub struct TrieRAM {
    nodes: HashMap<BlockHeaderHash, Vec<(TrieNodeType, TrieHash)>>,
    offset: u64,
    num_nodes: u64,
    block_header: BlockHeaderHash
}

// Trie in RAM without the serialization overhead
impl TrieRAM {
    pub fn new() -> TrieRAM {
        TrieRAM {
            nodes: HashMap::new(),
            offset: 0,
            num_nodes: 0,
            block_header: BlockHeaderHash([0u8; 32])
        }
    }

    pub fn from_block_header(bhh: &BlockHeaderHash) -> TrieRAM {
        TrieRAM {
            nodes: HashMap::new(),
            offset: 0,
            num_nodes: 0,
            block_header: bhh.clone(),
        }
    }
}

impl TrieStorage for TrieRAM {
    fn extend(&mut self, bhh: &BlockHeaderHash) -> Result<(), Error> {
        if self.nodes.contains_key(bhh) {
            return Err(Error::ExistsError);
        }
        test_debug!("Extend to {:?}", bhh);
        self.block_header = bhh.clone();
        self.offset = 0;
        self.num_nodes = 0;
        self.nodes.insert((*bhh).clone(), vec![]);
        Ok(())
    }

    fn open(&mut self, bhh: &BlockHeaderHash) -> Result<(), Error> {
        if !self.nodes.contains_key(bhh) {
            return Err(Error::NotFoundError);
        }
        self.block_header = bhh.clone();
        self.offset = 0;
        self.num_nodes = self.nodes.get(bhh).unwrap().len() as u64;
        Ok(())
    }

    fn tell(&self) -> BlockHeaderHash {
        self.block_header.clone()
    }

    fn format(&mut self) -> Result<(), Error> {
        self.nodes.clear();
        self.offset = 0;
        self.num_nodes = 0;
        Ok(())
    }

    fn format_block(&mut self, bhh: &BlockHeaderHash) -> Result<(), Error> {
        match self.nodes.get_mut(bhh) {
            Some(ref mut block_nodes) => {
                block_nodes.clear();
            },
            None => {}
        }
        self.block_header = bhh.clone();
        self.offset = 0;
        self.num_nodes = 0;
        Ok(())
    }

    fn read_node_hash(&mut self, ptr: &TriePtr) -> Result<TrieHash, Error> {
        match self.nodes.get(&self.block_header) {
            None => Err(Error::NotFoundError),
            Some(ref nodes) => {
                if ptr.ptr() >= (nodes.len() as u64) {
                    Err(Error::NotFoundError)
                }
                else {
                    Ok(nodes[ptr.ptr() as usize].1.clone())
                }
            }
        }
    }

    fn read_node(&mut self, ptr: &TriePtr) -> Result<(TrieNodeType, TrieHash), Error> {
        let disk_ptr = ftell(self)?;
        test_debug!("read_node({:?}): at {}: {:?}", &self.block_header, disk_ptr, ptr);
        match self.nodes.get(&self.block_header) {
            None => Err(Error::NotFoundError),
            Some(ref nodes) => {
                if ptr.ptr() >= (nodes.len() as u64) {
                    Err(Error::NotFoundError)
                }
                else {
                    Ok(nodes[ptr.ptr() as usize].clone())
                }
            }
        }
    }

    fn write_node(&mut self, node: &TrieNodeType, hash: TrieHash) -> Result<(), Error> {
        let disk_ptr = ftell(self)?;
        test_debug!("write_node({:?}): at {}: {:?} {:?}", &self.block_header, disk_ptr, &hash, node);
        match self.nodes.get_mut(&self.block_header) {
            None => Err(Error::NotFoundError),
            Some(ref mut nodes) => {
                if self.offset < (nodes.len() as u64) {
                    nodes[self.offset as usize] = (node.clone(), hash);
                    self.offset += 1;
                    Ok(())
                }
                else if self.offset == (nodes.len() as u64) {
                    nodes.push((node.clone(), hash));
                    self.offset += 1;
                    self.num_nodes += 1;
                    Ok(())
                }
                else {
                    Err(Error::NotFoundError)
                }
            }
        }
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

// ram-disk trie (for testing)
pub struct TrieIOBuffer {
    bufs: HashMap<BlockHeaderHash, Cursor<Vec<u8>>>,
    block_header: BlockHeaderHash
}

impl TrieIOBuffer {
    pub fn new(buf: Cursor<Vec<u8>>) -> TrieIOBuffer {
        let mut ret = TrieIOBuffer {
            bufs: HashMap::new(),
            block_header: BlockHeaderHash([0u8; 32])
        };
        ret.bufs.insert(ret.block_header.clone(), buf);
        ret
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
        Ok(())
    }

    fn open(&mut self, bhh: &BlockHeaderHash) -> Result<(), Error> {
        if !self.bufs.contains_key(bhh) {
            return Err(Error::NotFoundError);
        }
        self.block_header = bhh.clone();
        Ok(())
    }
    
    fn tell(&self) -> BlockHeaderHash {
        self.block_header.clone()
    }

    fn format(&mut self) -> Result<(), Error> {
        self.bufs.clear();
        Ok(())
    }

    fn format_block(&mut self, bhh: &BlockHeaderHash) -> Result<(), Error> {
        self.bufs.insert((*bhh).clone(), Cursor::new(vec![]));
        self.block_header = bhh.clone();
        Ok(())
    }

    fn read_node_hash(&mut self, ptr: &TriePtr) -> Result<TrieHash, Error> {
        match self.bufs.get_mut(&self.block_header) {
            Some(ref mut buf) => {
                read_node_hash(buf, ptr)
            },
            None => {
                Err(Error::NotFoundError)
            }
        }
    }

    fn read_node(&mut self, ptr: &TriePtr) -> Result<(TrieNodeType, TrieHash), Error> {
        test_debug!("read_node({:?}): {:?}", &self.block_header, ptr);
        match self.bufs.get_mut(&self.block_header) {
            Some(ref mut buf) => {
                read_nodetype(buf, ptr)
            },
            None => {
                Err(Error::NotFoundError)
            }
        }
    }
    
    fn write_node(&mut self, node: &TrieNodeType, hash: TrieHash) -> Result<(), Error> {
        let disk_ptr = ftell(self)?;
        test_debug!("write_node({:?}): at {}: {:?} {:?}", &self.block_header, disk_ptr, &hash, node);
        match self.bufs.get_mut(&self.block_header) {
            Some(ref mut buf) => {
                match node {
                    TrieNodeType::Leaf(ref data) => write_node_bytes(buf, data, hash),
                    TrieNodeType::Node4(ref data) => write_node_bytes(buf, data, hash),
                    TrieNodeType::Node16(ref data) => write_node_bytes(buf, data, hash),
                    TrieNodeType::Node48(ref data) => write_node_bytes(buf, data, hash),
                    TrieNodeType::Node256(ref data) => write_node_bytes(buf, data, hash),
                    TrieNodeType::BackPtr(ref data) => write_node_bytes(buf, data, hash),
                }
            },
            None => {
                Err(Error::NotFoundError)
            }
        }
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

pub struct Trie<S: TrieStorage> {
    pub path: String,
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
        let ptr = TriePtr::new(TrieNodeID::Node256, 0, 0);
        s.read_node(&ptr)
    }

    fn root_ptr() -> TriePtr {
        TriePtr::new(TrieNodeID::Node256, 0, 0)
    }

    fn read_node_hash(s: &mut S, ptr: &TriePtr) -> Result<TrieHash, Error> {
        s.read_node_hash(ptr)
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
            TrieNodeID::BackPtr => s.write_node(&node.try_as_backptr().unwrap(), hash),
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

    /*
    /// Get a value at the end of a path.
    /// NOTE: does _not_ follow TrieBackPtrs -- will return Ok(None) if encountered.
    fn get(s: &mut S, path: &TriePath) -> Result<Option<TrieLeaf>, Error> {
        test_debug!("Get {:?}", path);
        let mut c = TrieCursor::new(path);
        let (mut node, root_hash) = Trie::read_root(s)?;
        for _ in 0..c.path.len()+1 {
            test_debug!("get: at {:?} on {:?}", &node, path);
            let next_opt = Trie::walk_from(s, &node, &mut c)?;
            match next_opt {
                Some((_ptr, next_node, _next_node_hash)) => {
                    // keep walking
                    node = next_node;
                    continue;
                },
                None => {
                    // out of path.
                    if c.eop() {
                        // reached the end.  Did we find a leaf or a node?
                        match node {
                            TrieNodeType::Leaf(data) => {
                                // found!
                                test_debug!("get: found {:?} at {:?}", &data, path);
                                return Ok(Some(data));
                            },
                            _ => {
                                // Trie invariant violation -- a full path reached a non-leaf
                                panic!("Path reached a non-leaf");
                            }
                        }
                    }
                    else {
                        // path didn't match a node 
                        test_debug!("get: found nothing at {:?}", path);
                        return Ok(None);
                    }
                }
            }
        }

        // this cannot take more than TriePath.len() steps
        panic!("Trie has a cycle");
    }
    */

    /// Read a sequence of hashes given a node's ptrs.
    /// By construction, this will work even if the ptrs refer to BackPtrs (since BackPtr nodes
    /// have the hashes of the nodes they point to).
    fn read_node_hashes(s: &mut S, ptrs: &[TriePtr]) -> Result<Vec<TrieHash>, Error> {
        let mut ret = vec![];
        for i in 0..ptrs.len() {
            if ptrs[i].id() == TrieNodeID::Empty {
                // hash of empty string
                ret.push(TrieHash::from_data(&[]));
            }
            else {
                let h = Trie::read_node_hash(s, &ptrs[i])?;
                ret.push(h);
            }
        }
        Ok(ret)
    }

    /// Read a node's children's hashes.
    /// This only works for intermediate nodes and leafs (the latter of which have no children).
    /// A BackPtr cannot be handled since the node it refers to is in another Trie.
    fn get_children_hashes(s: &mut S, node: &TrieNodeType) -> Result<Vec<TrieHash>, Error> {
        match node {
            TrieNodeType::BackPtr(_) => {
                panic!("Cannot get the children hashes of a backptr");
            }
            TrieNodeType::Leaf(_) => {
                Ok(vec![])
            },
            TrieNodeType::Node4(ref data) => {
                let ret = Trie::read_node_hashes(s, &data.ptrs)?;
                Ok(ret)
            },
            TrieNodeType::Node16(ref data) => {
                let ret = Trie::read_node_hashes(s, &data.ptrs)?;
                Ok(ret)
            },
            TrieNodeType::Node48(ref data) => {
                let ret = Trie::read_node_hashes(s, &data.ptrs)?;
                Ok(ret)
            },
            TrieNodeType::Node256(ref data) => {
                let ret = Trie::read_node_hashes(s, &data.ptrs)?;
                Ok(ret)
            }
        }
    }

    /// Given a leaf, replace it.
    /// c must point to the value to replace
    fn replace_leaf(s: &mut S, c: &TrieCursor, value: &TrieLeaf) -> Result<TriePtr, Error> {
        let leaf_hash = get_node_hash(value, &vec![]);
        fseek(s, c.ptr().ptr())?;
        Trie::write_node(s, value, leaf_hash.clone())?;
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
       
        let leaf_ptr = TriePtr::new(TrieNodeID::Leaf, chr, ptr);
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
        let cur_leaf_new_ptr = TriePtr::new(TrieNodeID::Leaf, cur_leaf_chr, cur_leaf_disk_ptr);

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

        let new_leaf_ptr = TriePtr::new(TrieNodeID::Leaf, new_leaf_chr, new_leaf_disk_ptr);

        // append the Node4 that points to both of them, and put it after the new leaf
        let node4_disk_ptr = fseek_end(s)?;
        let mut node4_data = TrieNode4::new(&node4_path);

        assert!(node4_data.insert(&cur_leaf_new_ptr));
        assert!(node4_data.insert(&new_leaf_ptr));

        let node4_hash = get_node_hash(&node4_data, &vec![cur_leaf_hash, new_leaf_hash, TrieHash::from_data(&[]), TrieHash::from_data(&[])]);

        Trie::write_node(s, &node4_data, node4_hash.clone())?;

        let ret = TriePtr::new(TrieNodeID::Node4, node4_chr, node4_disk_ptr);
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

            let node_hashes = Trie::read_node_hashes(s, node_data.ptrs())?;
            let new_node_hash = get_node_hash(node_data, &node_hashes);

            fseek(s, c.ptr().ptr())?;
            Trie::write_node(s, node_data, new_node_hash)?;
            
            Ok(Some(c.ptr()))
        }

        match node {
            TrieNodeType::Leaf(_) => panic!("Cannot insert into leaf"),
            TrieNodeType::BackPtr(_) => panic!("Cannot insert into a backptr"),
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
        
            let node_hashes = Trie::read_node_hashes(s, new_node_data.ptrs())?;
            let new_node_hash = get_node_hash(new_node_data, &node_hashes);

            let new_node_disk_ptr = fseek_end(s)?;
            Trie::write_node(s, new_node_data, new_node_hash.clone())?;
            
            // give back the promoted node's ptr
            Ok(TriePtr::new(new_node_data.id(), node_ptr.chr(), new_node_disk_ptr))
        }

        // need to promote node 
        match node {
            TrieNodeType::Leaf(_) => panic!("Cannot insert into a leaf"),
            TrieNodeType::BackPtr(_) => panic!("Cannot insert into a backptr"),
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
            TrieNodeType::BackPtr(_) => panic!("Intermediate node should not be a backptr"),
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
        let leaf_ptr = TriePtr::new(TrieNodeID::Leaf, leaf_chr, leaf_disk_ptr);
        Trie::write_node(s, leaf, leaf_hash.clone())?;
       
        // update current node (node-X) and make a new path and ptr for it
        let cur_node_cur_ptr = c.ptr();
        let new_cur_node_disk_ptr = fseek_end(s)?;
        let new_cur_node_ptr = TriePtr::new(cur_node_cur_ptr.id(), new_cur_node_chr, new_cur_node_disk_ptr);

        fseek(s, cur_node_cur_ptr.ptr())?;
        let node_hashes = Trie::get_children_hashes(s, node)?;      // should be safe since this isn't a backptr
        let new_cur_node_hash = match node {
            TrieNodeType::Leaf(_) => panic!("Intermediate node should not be a leaf"),
            TrieNodeType::BackPtr(_) => panic!("Intermediate node should not be a backptr"),
            TrieNodeType::Node4(ref mut data) => {
                data.path = new_cur_node_path;
                get_node_hash(data, &node_hashes)
            },
            TrieNodeType::Node16(ref mut data) => {
                data.path = new_cur_node_path;
                get_node_hash(data, &node_hashes)
            },
            TrieNodeType::Node48(ref mut data) => {
                data.path = new_cur_node_path;
                get_node_hash(data, &node_hashes)
            },
            TrieNodeType::Node256(ref mut data) => {
                data.path = new_cur_node_path;
                get_node_hash(data, &node_hashes)
            }
        };

        // build node-X' -- same type of node, but will occupy less space than node-X since its
        // path is shorter
        let (new_node_id, new_node, new_node_hash) = match node {
            TrieNodeType::Leaf(_) => panic!("Tried to use a leaf as an intermediate node"),
            TrieNodeType::BackPtr(_) => panic!("Tried to use a backptr as an intermediate node"),
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
        fseek(s, cur_node_cur_ptr.ptr())?;
        Trie::write_nodetype(s, &new_node, new_node_hash.clone())?;

        // store node-X at the end
        fseek(s, new_cur_node_disk_ptr)?;
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

        match node {
            TrieNodeType::BackPtr(_) => {
                panic!("Cannot add value off of a BackPtr");
            },
            _ => {}
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
            let (mut node, cur_hash) = Trie::read_node(s, &ptr)?;

            // this child_ptr _must_ be in the node.
            let updated = match node {
                TrieNodeType::Leaf(_) => panic!("Leaf as intermediate (read {:?})", &ptr),
                TrieNodeType::BackPtr(_) => panic!("Backptr as intermediate (read {:?})", &ptr),
                TrieNodeType::Node4(ref mut data) => data.replace(&child_ptr),
                TrieNodeType::Node16(ref mut data) => data.replace(&child_ptr),
                TrieNodeType::Node48(ref mut data) => data.replace(&child_ptr),
                TrieNodeType::Node256(ref mut data) => data.replace(&child_ptr)
            };
            if !updated {
                test_debug!("FAILED TO UPDATE {:?} WITH {:?}: {:?}", &node, &child_ptr, c);
                assert!(updated);
            }

            let hashes = Trie::get_children_hashes(s, &node)?;

            fseek(s, ptr.ptr())?;

            let new_hash = match node {
                TrieNodeType::BackPtr(ref data) => {
                    unreachable!();
                }
                TrieNodeType::Leaf(ref data) => {
                    let h = get_node_hash(data, &hashes);
                    Trie::write_node(s, data, h.clone())?;
                    h
                },
                TrieNodeType::Node4(ref data) => {
                    let h = get_node_hash(data, &hashes);
                    Trie::write_node(s, data, h.clone())?;
                    h
                },
                TrieNodeType::Node16(ref data) => {
                    let h = get_node_hash(data, &hashes);
                    Trie::write_node(s, data, h.clone())?;
                    h
                },
                TrieNodeType::Node48(ref data) => {
                    let h = get_node_hash(data, &hashes);
                    Trie::write_node(s, data, h.clone())?;
                    h
                },
                TrieNodeType::Node256(ref data) => {
                    let h = get_node_hash(data, &hashes);
                    Trie::write_node(s, data, h.clone())?;
                    h
                }
            };
            
            test_debug!("update_root_hash: Updated {:?} with {:?} from {:?} to {:?}", &node, &child_ptr, &cur_hash, &new_hash);

            child_ptr = ptr;
        }

        // must be at the root
        assert_eq!(child_ptr, TriePtr::new(TrieNodeID::Node256,0,0));
        Ok(())
    }

    /*
    /// Try to insert a leaf.
    /// Promote nodes in the trie to make space if needed.
    /// NOTE: does not resolve BackPtrs -- use the MARF insert method for that.
    fn insert(s: &mut S, k: &TriePath, v: &TrieLeaf) -> Result<(), Error> {
        let mut value = v.clone();
        let mut c = TrieCursor::new(k);

        // walk to insertion point 
        let (mut node, root_hash) = Trie::read_root(s)?;
        let mut node_ptr = TriePtr::new(0,0,0);

        for _ in 0..c.path.len() {
            let next_opt = Trie::walk_from(s, &node, &mut c)?;
            match next_opt {
                Some((next_node_ptr, next_node, _next_node_hash)) => {
                    // keep walking
                    node = next_node;
                    node_ptr = next_node_ptr;
                    continue;
                },
                None => {
                    match node {
                        TrieNodeType::BackPtr(_) => {
                            // do nothing if this was a backptr 
                            return Err(Error::BackPtrError);
                        }
                        _ => {
                            // walked to the end of the path -- cursor points to the insertion point
                            fseek(s, node_ptr.ptr())?;
                            Trie::add_value(s, &mut c, &mut value)?;
                            Trie::update_root_hash(s, &c)?;
                            break;
                        }
                    };
                }
            }
        }
        
        Ok(())
    }
    */
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

    /// Given a list of ptrs, generate TrieBackPtrs for them, write them out,
    /// and return a list of ptrs to them.
    /// The previous and current Tries must both exist.
    fn write_backptr_children(s: &mut S, ptrs: &[TriePtr], prev_block_hash: &BlockHeaderHash, cur_block_hash: &BlockHeaderHash) -> Result<(Vec<TriePtr>, Vec<TrieHash>), Error> {
        s.open(prev_block_hash)?;

        let mut new_ptrs = vec![];
        let mut new_backptrs = vec![];
        let mut hashes = vec![];
        for i in 0..ptrs.len() {
            if ptrs[i].id() == TrieNodeID::BackPtr {
                // resolve backptrs eagerly
                let (backptr_node, hash) = s.read_node(&ptrs[i])?;
                match backptr_node {
                    TrieNodeType::BackPtr(ref backptr) => {
                        test_debug!("Eager copy {:?}", backptr);
                        hashes.push(hash);
                        new_ptrs.push(TriePtr::new(TrieNodeID::BackPtr, ptrs[i].chr(), 0));
                        new_backptrs.push(backptr.clone());
                    },
                    _ => {
                        return Err(Error::CorruptionError);
                    }
                }
            }
            else if ptrs[i].id() != TrieNodeID::Empty {
                // intermediate or leaf node
                let hash = s.read_node_hash(&ptrs[i])?;
                let new_backptr = TrieBackPtr::new(&prev_block_hash, &ptrs[i]);
                let new_ptr = TriePtr::new(TrieNodeID::BackPtr, ptrs[i].chr(), 0);

                hashes.push(hash);
                new_ptrs.push(new_ptr);
                
                new_backptrs.push(new_backptr);
            }
            else {
                hashes.push(TrieHash::from_data(&[]));
                new_ptrs.push(TriePtr::new(TrieNodeID::Empty,0,0));
            }
        }

        s.open(cur_block_hash)?;
        let mut j = 0;
        for i in 0..ptrs.len() {
            if ptrs[i].id() != TrieNodeID::Empty {
                let disk_ptr = fseek_end(s)?;
                new_ptrs[i].ptr = disk_ptr;
                s.write_node(&TrieNodeType::BackPtr(new_backptrs[j].clone()), hashes[i].clone())?;
                j += 1;
            }
        }
        Ok((new_ptrs, hashes))
    }

    /// Make a new TrieNodeType with BackPtrs to an existing TrieNodeType
    /// Only works for intermediate nodes.
    /// s will point to cur_block_hash at the end of this method.
    fn write_backptrs(s: &mut S, node: &TrieNodeType, prev_block_hash: &BlockHeaderHash, cur_block_hash: &BlockHeaderHash) -> Result<(TrieNodeType, Vec<TrieHash>), Error> {
        test_debug!("Begin write backptr children for {:?} from {:?} to {:?}", node, prev_block_hash, cur_block_hash);
        let res = match node {
            TrieNodeType::Node4(ref node_data) => {
                let mut new_node_data = node_data.clone();
                let (new_ptrs, new_hashes) = MARF::write_backptr_children(s, new_node_data.ptrs(), prev_block_hash, cur_block_hash)?;
                new_node_data.ptrs.copy_from_slice(&new_ptrs[..]);
                (TrieNodeType::Node4(new_node_data), new_hashes)
            },
            TrieNodeType::Node16(ref node_data) => {
                let mut new_node_data = node_data.clone();
                let (new_ptrs, new_hashes) = MARF::write_backptr_children(s, new_node_data.ptrs(), prev_block_hash, cur_block_hash)?;
                new_node_data.ptrs.copy_from_slice(&new_ptrs[..]);
                (TrieNodeType::Node16(new_node_data), new_hashes)
            },
            TrieNodeType::Node48(ref node_data) => {
                let mut new_node_data = node_data.clone();
                let (new_ptrs, new_hashes) = MARF::write_backptr_children(s, new_node_data.ptrs(), prev_block_hash, cur_block_hash)?;
                new_node_data.ptrs.copy_from_slice(&new_ptrs[..]);
                (TrieNodeType::Node48(new_node_data), new_hashes)
            },
            TrieNodeType::Node256(ref node_data) => {
                let mut new_node_data = node_data.clone();
                let (new_ptrs, new_hashes) = MARF::write_backptr_children(s, new_node_data.ptrs(), prev_block_hash, cur_block_hash)?;
                new_node_data.ptrs.copy_from_slice(&new_ptrs[..]);
                (TrieNodeType::Node256(new_node_data), new_hashes)
            },
            TrieNodeType::Leaf(_) => {
                panic!("Tried to write backptrs for a leaf");
            },
            TrieNodeType::BackPtr(_) => {
                panic!("Tried to write backptrs for a backptr");
            },
        };

        assert_eq!(s.tell(), *cur_block_hash);
        test_debug!("End write backptr children for {:?} from {:?} to {:?}", node, prev_block_hash, cur_block_hash);
        Ok(res)
    }

    fn resolve_backptr(s: &mut S, backptr: &TrieBackPtr) -> Result<(TrieNodeType, TrieHash), Error> {
        test_debug!("Begin resolve backptr {:?}", backptr);
        s.open(&backptr.block_hash)?;
        let (next_node, next_node_hash) = s.read_node(&backptr.ptr)?;

        // sanity check -- this can't be another backptr
        match next_node {
            TrieNodeType::BackPtr(_) => {
                return Err(Error::InvalidNodeError);
            }
            _ => {}
        }

        test_debug!("End resolve backptr: {:?} --> {:?}", backptr, next_node);
        Ok((next_node, next_node_hash))
    }


    /// Copy an intermediate node from a prior Trie to this Trie, given a backptr.
    /// Copies over BackPtrs for its children, as well as their (actual childrens') hashes
    /// The target trie must already exist.
    /// Returns InvalidNodeError if this is a leaf
    fn backptr_copy(s: &mut S, target_block_hash: &BlockHeaderHash, backptr: &TrieBackPtr) -> Result<(TrieNodeType, TriePtr), Error> {
        // backptr encountered.  shunt to that trie, get the node,
        // copy it over to _this_ Trie
        test_debug!("Begin backptr copy {:?} {:?}", target_block_hash, backptr);
        let (next_node, next_node_hash) = MARF::resolve_backptr(s, backptr)?;
        
        // can't be a leaf
        match next_node {
            TrieNodeType::Leaf(_) => {
                return Err(Error::LeafError);
            }
            _ => {}
        }

        // port this node over
        let (new_node, node_hashes) = MARF::write_backptrs(s, &next_node, &backptr.block_hash, target_block_hash)?;

        // store a _new_ node to this trie with backptrs to its children
        let node_hash = match new_node {
            TrieNodeType::Node4(ref data) => {
                get_node_hash(data, &node_hashes)
            },
            TrieNodeType::Node16(ref data) => {
                get_node_hash(data, &node_hashes)
            },
            TrieNodeType::Node48(ref data) => {
                get_node_hash(data, &node_hashes)
            },
            TrieNodeType::Node256(ref data) => {
                get_node_hash(data, &node_hashes)
            },
            TrieNodeType::Leaf(ref data) => {
                unreachable!();
            },
            TrieNodeType::BackPtr(_) => {
                unreachable!();
            }
        };

        s.open(target_block_hash)?;
        let new_node_disk_ptr = fseek_end(s)?;
        s.write_node(&new_node, node_hash)?;

        let new_ptr = TriePtr::new(backptr.ptr.id(), backptr.ptr.chr(), new_node_disk_ptr);

        test_debug!("End Backptr copy: {:?} at {:?} into {:?}", &new_node, &new_ptr, target_block_hash);
        Ok((new_node, new_ptr))
    }

    /// Walk down this MARF at the given block hash, doing a copy-on-write for intermediate nodes in this block's Trie from any prior Tries.
    fn walk_cow(s: &mut S, block_hash: &BlockHeaderHash, k: &TriePath) -> Result<TrieCursor, Error> {
        let cur_bhh = s.tell();
        MARF::switch_trie(s, &cur_bhh, block_hash)?;

        let mut c = TrieCursor::new(k);

        // walk to insertion point 
        let (mut node, _) = Trie::read_root(s)?;
        let mut node_ptr = TriePtr::new(0,0,0);

        let mut expected_path_len = c.path.len() + 1;   // will be incremented if we find a backptr, since it's one more step
        let mut i = 0;
        while i <= expected_path_len {
            i += 1;
            
            let next_opt = Trie::walk_from(s, &node, &mut c)?;
            match next_opt {
                Some((next_node_ptr, next_node, _next_node_hash)) => {
                    // keep walking
                    node = next_node;
                    node_ptr = next_node_ptr;
                    continue;
                },
                None => {
                    let (next_node, next_node_ptr) = match node {
                        TrieNodeType::BackPtr(ref data) => {
                            // Copy over intermediate node place-holders and keep going.
                            // If this is a leaf, then we're done.
                            let (next_node, next_node_ptr) = match MARF::backptr_copy(s, block_hash, data) {
                                Ok((next_node, next_node_ptr)) => (next_node, next_node_ptr),
                                Err(Error::LeafError) => {
                                    // this backptr points to a leaf -- no COW done.
                                    s.open(&data.block_hash)?;
                                    fseek(s, data.ptr.ptr())?;
                                    return Ok(c);
                                },
                                Err(e) => {
                                    return Err(e);
                                }
                            };

                            test_debug!("Shunt to {:?} to walk from {:?}", &data.block_hash, &next_node_ptr);
                           
                            // switch back over to _this_ Trie, since we COW'ed the missing node
                            s.open(block_hash)?;
                            c.retarget(&next_node, &next_node_ptr, &s.tell());

                            // walk again 
                            expected_path_len += 1;
                            (next_node, next_node_ptr)
                        },
                        _ => {
                            // either found a leaf, or we're out of path
                            s.open(block_hash)?;
                            fseek(s, node_ptr.ptr())?;
                            return Ok(c);
                        }
                    };
                    node = next_node;
                    node_ptr = next_node_ptr;
                }
            }
        }

        test_debug!("Trie has a cycle");
        return Err(Error::CorruptionError);
    }

    /// Walk down this MARF at the given block hash, resolving backptrs to previous tries.
    /// Return the cursor and the last node visited
    fn walk(s: &mut S, block_hash: &BlockHeaderHash, k: &TriePath) -> Result<(TrieCursor, TrieNodeType), Error> {
        s.open(block_hash)?;

        let mut c = TrieCursor::new(k);

        // walk to insertion point 
        let (mut node, _) = Trie::read_root(s)?;
        let mut node_ptr = TriePtr::new(0,0,0);

        let mut expected_path_len = c.path.len() + 1;   // will be incremented if we find a backptr, since it's one more step
        let mut i = 0;
        while i <= expected_path_len {
            i += 1;
            
            let next_opt = Trie::walk_from(s, &node, &mut c)?;
            match next_opt {
                Some((next_node_ptr, next_node, _)) => {
                    // keep walking 
                    node = next_node;
                    node_ptr = next_node_ptr;
                    continue;
                },
                None => {
                    let (next_node, next_node_ptr) = match node {
                        TrieNodeType::BackPtr(ref backptr) => {
                            // backptr encountered.  shunt to that trie and get the next node
                            s.open(&backptr.block_hash)?;
                            let (next_node, _) = s.read_node(&backptr.ptr)?;
                            c.retarget(&next_node, &backptr.ptr, &s.tell());
                            
                            // will take one more step
                            expected_path_len += 1;
                            (next_node, backptr.ptr.clone())
                        },
                        _ => {
                            // either found a leaf, or out of path
                            fseek(s, node_ptr.ptr())?;
                            return Ok((c, node));
                        }
                    };
                    node = next_node;
                    node_ptr = next_node_ptr;
                }
            }
        }

        test_debug!("Trie has a cycle");
        return Err(Error::CorruptionError);
    }

    pub fn format(s: &mut S, first_block_hash: &BlockHeaderHash) -> Result<(), Error> {
        Trie::format(s, first_block_hash)
    }

    /// create or open a particular Trie.
    /// If the trie doesn't exist, then extend it from the current Trie and create a root node that
    /// has back pointers to its immediate children in the current trie.
    fn switch_trie(s: &mut S, cur_bhh: &BlockHeaderHash, new_bhh: &BlockHeaderHash) -> Result<(), Error> {
        match s.open(new_bhh) {
            Ok(_) => {
                test_debug!("Switch to Trie {:?}", new_bhh);
                Ok(())
            }
            Err(e) => {
                match e {
                    Error::NotFoundError => {
                        s.open(cur_bhh)?;
                        let (cur_root_node, cur_root_hash) = s.read_node(&TriePtr::new(TrieNodeID::Node256, 0, 0))?;
                        let root_node = match cur_root_node {
                            TrieNodeType::Node256(data) => data,
                            _ => panic!("Root node is not a Node256 in {:?}", cur_bhh)
                        };
                        
                        let mut new_root_ptrs = [TriePtr::default(); 256];
                        let mut hashes = Vec::with_capacity(256);
                        let mut new_backptrs = Vec::with_capacity(256);
                        let cur_ptrs = root_node.ptrs();

                        for i in 0..256 {
                            if cur_ptrs[i].id() == TrieNodeID::BackPtr {
                                // resolve backptrs eagerly
                                let (backptr_node, hash) = s.read_node(&cur_ptrs[i])?;
                                match backptr_node {
                                    TrieNodeType::BackPtr(ref backptr) => {
                                        test_debug!("Eager copy {:?}", &backptr_node);
                                        hashes.push(hash);
                                        new_root_ptrs[i] = TriePtr::new(TrieNodeID::BackPtr, cur_ptrs[i].chr(), 0);
                                        new_backptrs.push(backptr.clone());
                                    },
                                    _ => {
                                        return Err(Error::CorruptionError);
                                    }
                                }
                            }
                            else if cur_ptrs[i].id() != TrieNodeID::Empty {                                
                                let hash = s.read_node_hash(&cur_ptrs[i])?;
                                let new_backptr = TrieBackPtr::new(&cur_bhh, &cur_ptrs[i]);
                                
                                new_root_ptrs[i] = TriePtr::new(TrieNodeID::BackPtr, cur_ptrs[i].chr(), 0); // NOTE: these are the consensus bytes for the ptr -- id and chr
                                hashes.push(hash);
                                new_backptrs.push(new_backptr);
                            }
                            else {
                                hashes.push(TrieHash::from_data(&[]));
                            }
                        }

                        s.extend(new_bhh)?;
                        fseek(s, 0)?;

                        // put root node in place (will update after writing in backptrs)
                        let mut new_root = TrieNode256::new(&root_node.path);
                        s.write_node(&TrieNodeType::Node256(new_root.clone()), TrieHash::from_data(&[]))?;

                        let mut j = 0;
                        for i in 0..256 {
                            if new_root_ptrs[i].id() != TrieNodeID::Empty {
                                let disk_ptr = fseek_end(s)?;
                                new_root_ptrs[i].ptr = disk_ptr;
                                s.write_node(&TrieNodeType::BackPtr(new_backptrs[j].clone()), hashes[i].clone())?;
                                j += 1;
                            }
                        }

                        // update root node with correct hash and pointers
                        new_root.ptrs.copy_from_slice(&mut new_root_ptrs);
                        let new_root_hash = get_node_hash(&new_root, &hashes);
                        fseek(s, 0)?;
                        s.write_node(&TrieNodeType::Node256(new_root), new_root_hash)?;

                        Ok(())
                    },
                    _ => Err(e)
                }
            }
        }
    }

    pub fn get(s: &mut S, block_hash: &BlockHeaderHash, k: &TriePath) -> Result<Option<TrieLeaf>, Error> {
        s.open(block_hash)?;
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
                    panic!("Path reached a non-leaf");
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

    // TODO: insert batch (avoid excessive re-hashes)
}


#[derive(Clone)]
pub enum TrieMerkleProofType {
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
            TrieMerkleProofType::Node4((ref chr, ref node, ref hashes)) => write!(f, "TrieMerkleProofType::Node4({}, {:?}, {})", chr, node, hashes_fmt(hashes)),
            TrieMerkleProofType::Node16((ref chr, ref node, ref hashes)) => write!(f, "TrieMerkleProofType::Node16({}, {:?}, {})", chr, node, hashes_fmt(hashes)),
            TrieMerkleProofType::Node48((ref chr, ref node, ref hashes)) => write!(f, "TrieMerkleProofType::Node48({}, {:?}, {})", chr, node, hashes_fmt(hashes)),
            TrieMerkleProofType::Node256((ref chr, ref node, ref hashes)) => write!(f, "TrieMerkleProofType::Node256({}, {:?}, {})", chr, node, hashes_fmt(hashes)),
            TrieMerkleProofType::Leaf((ref chr, ref node)) => write!(f, "TrieMerkleProofType::Leaf({}, {:?})", chr, node),
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
    /// to the previous node.  Does not handle backptrs.
    fn ptr_to_proof_node<S: TrieStorage + Seek>(s: &mut S, ptr: &TriePtr, chr: u8) -> Result<TrieMerkleProofType, Error> {
        let (node, node_hash) = Trie::read_node(s, &ptr)?;
        let all_hashes = Trie::get_children_hashes(s, &node)?;

        let proof_node = match node {
            TrieNodeType::BackPtr(ref data) => {
                // shouldn't happen anyway
                panic!("Cannot make a proof node from a backptr (at {:?}", ptr);
            },
            TrieNodeType::Leaf(ref data) => {
                TrieMerkleProofType::Leaf((chr, data.clone()))
            },
            TrieNodeType::Node4(ref data) => {
                let mut hashes = vec![];
                assert!(all_hashes.len() == data.ptrs.len());

                for i in 0..4 {
                    if data.ptrs[i].id() == TrieNodeID::Empty {
                        hashes.push(TrieHash::from_data(&[]));
                    }
                    else if data.ptrs[i].chr() != chr {
                        hashes.push(all_hashes[i].clone());
                    }
                }
                assert_eq!(hashes.len(), 3);

                let mut hash_slice = [TrieHash::from_data(&[]); 3];
                hash_slice.copy_from_slice(&hashes[0..3]);

                TrieMerkleProofType::Node4((chr, data.clone(), hash_slice))
            },
            TrieNodeType::Node16(ref data) => {
                let mut hashes = vec![];
                assert!(all_hashes.len() == data.ptrs.len());

                for i in 0..16 {
                    if data.ptrs[i].id() == TrieNodeID::Empty {
                        hashes.push(TrieHash::from_data(&[]));
                    }
                    else if data.ptrs[i].chr() != chr {
                        hashes.push(all_hashes[i].clone());
                    }
                }
                assert_eq!(hashes.len(), 15);
                
                let mut hash_slice = [TrieHash::from_data(&[]); 15];
                hash_slice.copy_from_slice(&hashes[0..15]);

                TrieMerkleProofType::Node16((chr, data.clone(), hash_slice))
            },
            TrieNodeType::Node48(ref data) => {
                let mut hashes = vec![];
                assert!(all_hashes.len() == data.ptrs.len());

                for i in 0..48 {
                    if data.ptrs[i].id() == TrieNodeID::Empty {
                        hashes.push(TrieHash::from_data(&[]));
                    }
                    else if data.ptrs[i].chr() != chr {
                        hashes.push(all_hashes[i].clone());
                    }
                }
                assert_eq!(hashes.len(), 47);
                
                let mut hash_slice = [TrieHash::from_data(&[]); 47];
                hash_slice.copy_from_slice(&hashes[0..47]);

                TrieMerkleProofType::Node48((chr, data.clone(), hash_slice))
            },
            TrieNodeType::Node256(ref data) => {
                let mut hashes = vec![];
                assert!(all_hashes.len() == data.ptrs.len());

                for i in 0..256 {
                    if data.ptrs[i].id() == TrieNodeID::Empty {
                        hashes.push(TrieHash::from_data(&[]));
                    }
                    else if data.ptrs[i].chr() != chr {
                        hashes.push(all_hashes[i].clone());
                    }
                }
                assert_eq!(hashes.len(), 255);

                let mut hash_slice = [TrieHash::from_data(&[]); 255];
                hash_slice.copy_from_slice(&hashes[0..255]);

                TrieMerkleProofType::Node256((chr, data.clone(), hash_slice))
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
        let mut chr = c.chr().unwrap();
        
        while ptrs.len() > 0 {
            ptr = match ptrs.pop() {
                Some(p) => p,
                None => panic!("out of ptrs")
            };

            match block_hashes.pop() {
                Some(h) => {
                    s.open(&h)?;
                }
                None => {
                    // at root
                    assert_eq!(ptrs.len(), 0);
                    s.open(root_block_header)?;
                }
            };

            let proof_node = TrieMerkleProof::ptr_to_proof_node(s, &ptr, chr)?;
            proof.push(proof_node);
            chr = ptr.chr();
        }
        
        // must have ended on root 
        assert_eq!(ptr, TriePtr::new(TrieNodeID::Node256, 0, 0));
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
                all_hashes.push(hashes[ih].clone());
                ih += 1;
            }
        }
        if all_hashes.len() != count {
            test_debug!("verify_get_hash: {} != {}", all_hashes.len(), count);
            return None
        }

        Some(get_node_hash(node, &all_hashes))
    }

    pub fn verify(&self, path: &TriePath, value: &TrieLeaf, root_hash: &TrieHash) -> bool {
        let mut hash = get_node_hash(value, &vec![]);
        for j in 0..self.0.len() {
            let next_hash = match self.0[j] {
                TrieMerkleProofType::Leaf((ref chr, ref node)) => {
                    let hopt = TrieMerkleProof::verify_get_hash(node, &hash, *chr, &vec![], 0);
                    match hopt {
                        None => {
                            return false;
                        },
                        Some(h) => h
                    }
                },
                TrieMerkleProofType::Node4((ref chr, ref node, ref hashes)) => {
                    let hopt = TrieMerkleProof::verify_get_hash(node, &hash, *chr, hashes, 4);
                    match hopt {
                        None => {
                            return false;
                        },
                        Some(h) => h
                    }
                },
                TrieMerkleProofType::Node16((ref chr, ref node, ref hashes)) => {
                    let hopt = TrieMerkleProof::verify_get_hash(node, &hash, *chr, hashes, 16);
                    match hopt {
                        None => {
                            return false;
                        }
                        Some(h) => h
                    }
                },
                TrieMerkleProofType::Node48((ref chr, ref node, ref hashes)) => {
                    let hopt = TrieMerkleProof::verify_get_hash(node, &hash, *chr, hashes, 48);
                    match hopt {
                        None => {
                            return false;
                        }
                        Some(h) => h
                    }
                },
                TrieMerkleProofType::Node256((ref chr, ref node, ref hashes)) => {
                    let hopt = TrieMerkleProof::verify_get_hash(node, &hash, *chr, hashes, 256);
                    match hopt {
                        None => {
                            return false;
                        }
                        Some(h) => h
                    }
                },
            };
            hash = next_hash;
        }

        test_debug!("verify: {:?} =?= {:?}", hash, root_hash);
        hash == *root_hash
    }
}
#[cfg(test)]
mod test {

    use super::*;

    use std::io::{
        Cursor
    };

    use std::collections::HashMap;

    fn dump_trie<S: TrieStorage + Seek>(s: &mut S) -> () {

        test_debug!("\n----- BEGIN TRIE ------");

        fn space(cnt: usize) -> String {
            let mut ret = vec![];
            for _ in 0..cnt {
                ret.push(" ".to_string());
            }
            ret.join("")
        }

        fseek(s, 0).unwrap();

        let mut frontier : Vec<(TrieNodeType, usize)> = vec![];
        let (root, _) = Trie::read_root(s).unwrap();
        frontier.push((root, 0));

        while frontier.len() > 0 {
            let (next, depth) = frontier.pop().unwrap();
            let (ptrs, path_len) = match next {
                TrieNodeType::BackPtr(ref data) => {
                    test_debug!("{}{:?}", &space(depth), data);
                    (vec![], 0)
                },
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
                let (child_node, _) = Trie::read_node(s, ptr).unwrap();
                frontier.push((child_node, depth + path_len + 1));
            }
        }
        
        test_debug!("----- END TRIE ------\n");
    }

    fn merkle_test<S: TrieStorage + Seek>(s: &mut S, path: &Vec<u8>, value: &Vec<u8>) -> () {
        let (_, root_hash) = Trie::read_root(s).unwrap();
        let triepath = TriePath::from_bytes(&path[..]).unwrap();
        let value_leaf = TrieLeaf::new(&vec![], &value);

        let block_header = BlockHeaderHash([0u8; 32]);
        s.open(&block_header).unwrap();

        let proof = TrieMerkleProof::from_path(s, &triepath).unwrap();
        assert!(proof.verify(&triepath, &value_leaf, &root_hash));
    }
    
    fn merkle_test_marf<S: TrieStorage + Seek>(s: &mut S, header: &BlockHeaderHash, path: &Vec<u8>, value: &Vec<u8>) -> () {
        s.open(header).unwrap();
        let (_, root_hash) = Trie::read_root(s).unwrap();
        let triepath = TriePath::from_bytes(&path[..]).unwrap();
        let value_leaf = TrieLeaf::new(&vec![], &value);

        let proof = TrieMerkleProof::from_path(s, &triepath).unwrap();
        assert!(proof.verify(&triepath, &value_leaf, &root_hash));
    }

    #[test]
    fn trieptr_to_bytes() {
        let t = TriePtr::new(0x11, 0x22, 0x33445566778899aa);
        let t_bytes = vec![0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xaa];
        assert_eq!(t.to_bytes(), t_bytes);
        assert_eq!(TriePtr::from_bytes(&t_bytes), t);
    }

    #[test]
    fn trie_node4_to_bytes() {
        let mut node4 = TrieNode4::new(&vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19]);
        for i in 0..3 {
            assert!(node4.insert(&TriePtr::new(TrieNodeID::Node16, (i+1) as u8, (i+2) as u64)));
        }
        let node4_bytes = vec![
            // node ID
            TrieNodeID::Node4,
            // ptrs (4)
            TrieNodeID::Node16, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x2,
            TrieNodeID::Node16, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x3,
            TrieNodeID::Node16, 0x03, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x4,
            TrieNodeID::Empty, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            // path length 
            0x14,
            // path 
            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10, 0x11, 0x12, 0x13
        ];
        let mut node4_stream = Cursor::new(node4_bytes.clone());

        assert_eq!(node4.to_bytes(), node4_bytes);
        assert_eq!(TrieNode4::from_bytes(&mut node4_stream).unwrap(), node4);
    }
    
    #[test]
    fn trie_node4_to_consensus_bytes() {
        let mut node4 = TrieNode4::new(&vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19]);
        for i in 0..3 {
            assert!(node4.insert(&TriePtr::new(TrieNodeID::Node16, (i+1) as u8, (i+2) as u64)));
        }
        let node4_bytes = vec![
            // node ID
            TrieNodeID::Node4,
            // ptrs (4)
            TrieNodeID::Node16, 0x01,
            TrieNodeID::Node16, 0x02,
            TrieNodeID::Node16, 0x03,
            TrieNodeID::Empty, 0x00,
            // path length 
            0x14,
            // path 
            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10, 0x11, 0x12, 0x13
        ];
        let node4_stream = Cursor::new(node4_bytes.clone());

        assert_eq!(node4.to_consensus_bytes(), node4_bytes);
    }

    #[test]
    fn trie_node16_to_bytes() {
        let mut node16 = TrieNode16::new(&vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19]);
        for i in 0..15 {
            assert!(node16.insert(&TriePtr::new(TrieNodeID::Node48, (i+1) as u8, (i+2) as u64)));
        }
        let node16_bytes = vec![
            // node ID
            TrieNodeID::Node16,
            // ptrs (16)
            TrieNodeID::Node48, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x2,
            TrieNodeID::Node48, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x3,
            TrieNodeID::Node48, 0x03, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x4,
            TrieNodeID::Node48, 0x04, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x5,
            TrieNodeID::Node48, 0x05, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x6,
            TrieNodeID::Node48, 0x06, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x7,
            TrieNodeID::Node48, 0x07, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x8,
            TrieNodeID::Node48, 0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x9,
            TrieNodeID::Node48, 0x09, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xa,
            TrieNodeID::Node48, 0x0a, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xb,
            TrieNodeID::Node48, 0x0b, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xc,
            TrieNodeID::Node48, 0x0c, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xd,
            TrieNodeID::Node48, 0x0d, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xe,
            TrieNodeID::Node48, 0x0e, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xf,
            TrieNodeID::Node48, 0x0f, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x10,
            TrieNodeID::Empty, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            // path length 
            0x14,
            // path 
            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10, 0x11, 0x12, 0x13
        ];
        let mut node16_stream = Cursor::new(node16_bytes.clone());

        assert_eq!(node16.to_bytes(), node16_bytes);
        assert_eq!(TrieNode16::from_bytes(&mut node16_stream).unwrap(), node16);
    }
    
    #[test]
    fn trie_node16_to_consensus_bytes() {
        let mut node16 = TrieNode16::new(&vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19]);
        for i in 0..15 {
            assert!(node16.insert(&TriePtr::new(TrieNodeID::Node48, (i+1) as u8, (i+2) as u64)));
        }
        let node16_bytes = vec![
            // node ID
            TrieNodeID::Node16,
            // ptrs (16)
            TrieNodeID::Node48, 0x01,
            TrieNodeID::Node48, 0x02, 
            TrieNodeID::Node48, 0x03, 
            TrieNodeID::Node48, 0x04,
            TrieNodeID::Node48, 0x05, 
            TrieNodeID::Node48, 0x06, 
            TrieNodeID::Node48, 0x07, 
            TrieNodeID::Node48, 0x08, 
            TrieNodeID::Node48, 0x09, 
            TrieNodeID::Node48, 0x0a, 
            TrieNodeID::Node48, 0x0b,
            TrieNodeID::Node48, 0x0c,
            TrieNodeID::Node48, 0x0d,
            TrieNodeID::Node48, 0x0e,
            TrieNodeID::Node48, 0x0f,
            TrieNodeID::Empty, 0x00,
            // path length 
            0x14,
            // path 
            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10, 0x11, 0x12, 0x13
        ];
        let node16_stream = Cursor::new(node16_bytes.clone());
        assert_eq!(node16.to_consensus_bytes(), node16_bytes);
    }

    #[test]
    fn trie_node48_to_bytes() {
        let mut node48 = TrieNode48::new(&vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19]);
        for i in 0..47 {
            assert!(node48.insert(&TriePtr::new(TrieNodeID::Node256, (i+1) as u8, (i+2) as u64)));
        }
        let node48_bytes = vec![
            // node ID
            TrieNodeID::Node48,
            // ptrs (48)
            TrieNodeID::Node256, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x2,
            TrieNodeID::Node256, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x3,
            TrieNodeID::Node256, 0x03, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x4,
            TrieNodeID::Node256, 0x04, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x5,
            TrieNodeID::Node256, 0x05, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x6,
            TrieNodeID::Node256, 0x06, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x7,
            TrieNodeID::Node256, 0x07, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x8,
            TrieNodeID::Node256, 0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x9,
            TrieNodeID::Node256, 0x09, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xa,
            TrieNodeID::Node256, 0x0a, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xb,
            TrieNodeID::Node256, 0x0b, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xc,
            TrieNodeID::Node256, 0x0c, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xd,
            TrieNodeID::Node256, 0x0d, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xe,
            TrieNodeID::Node256, 0x0e, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xf,
            TrieNodeID::Node256, 0x0f, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x10,
            TrieNodeID::Node256, 0x10, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x11,
            TrieNodeID::Node256, 0x11, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x12,
            TrieNodeID::Node256, 0x12, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x13,
            TrieNodeID::Node256, 0x13, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x14,
            TrieNodeID::Node256, 0x14, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x15,
            TrieNodeID::Node256, 0x15, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x16,
            TrieNodeID::Node256, 0x16, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x17,
            TrieNodeID::Node256, 0x17, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x18,
            TrieNodeID::Node256, 0x18, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x19,
            TrieNodeID::Node256, 0x19, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x1a,
            TrieNodeID::Node256, 0x1a, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x1b,
            TrieNodeID::Node256, 0x1b, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x1c,
            TrieNodeID::Node256, 0x1c, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x1d,
            TrieNodeID::Node256, 0x1d, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x1e,
            TrieNodeID::Node256, 0x1e, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x1f,
            TrieNodeID::Node256, 0x1f, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x20,
            TrieNodeID::Node256, 0x20, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x21,
            TrieNodeID::Node256, 0x21, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x22,
            TrieNodeID::Node256, 0x22, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x23,
            TrieNodeID::Node256, 0x23, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x24,
            TrieNodeID::Node256, 0x24, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x25,
            TrieNodeID::Node256, 0x25, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x26,
            TrieNodeID::Node256, 0x26, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x27,
            TrieNodeID::Node256, 0x27, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x28,
            TrieNodeID::Node256, 0x28, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x29,
            TrieNodeID::Node256, 0x29, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x2a,
            TrieNodeID::Node256, 0x2a, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x2b,
            TrieNodeID::Node256, 0x2b, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x2c,
            TrieNodeID::Node256, 0x2c, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x2d,
            TrieNodeID::Node256, 0x2d, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x2e,
            TrieNodeID::Node256, 0x2e, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x2f,
            TrieNodeID::Node256, 0x2f, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x30,
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

        assert_eq!(node48.to_bytes(), node48_bytes);
        assert_eq!(TrieNode48::from_bytes(&mut node48_stream).unwrap(), node48);
    }

    #[test]
    fn trie_node48_to_consensus_bytes() {
        let mut node48 = TrieNode48::new(&vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19]);
        for i in 0..47 {
            assert!(node48.insert(&TriePtr::new(TrieNodeID::Node256, (i+1) as u8, (i+2) as u64)));
        }
        let node48_bytes = vec![
            // node ID
            TrieNodeID::Node48,
            // ptrs (48)
            TrieNodeID::Node256, 0x01, 
            TrieNodeID::Node256, 0x02, 
            TrieNodeID::Node256, 0x03,
            TrieNodeID::Node256, 0x04, 
            TrieNodeID::Node256, 0x05,
            TrieNodeID::Node256, 0x06, 
            TrieNodeID::Node256, 0x07,
            TrieNodeID::Node256, 0x08, 
            TrieNodeID::Node256, 0x09,
            TrieNodeID::Node256, 0x0a,
            TrieNodeID::Node256, 0x0b,
            TrieNodeID::Node256, 0x0c,
            TrieNodeID::Node256, 0x0d,
            TrieNodeID::Node256, 0x0e,
            TrieNodeID::Node256, 0x0f,
            TrieNodeID::Node256, 0x10,
            TrieNodeID::Node256, 0x11,
            TrieNodeID::Node256, 0x12,
            TrieNodeID::Node256, 0x13,
            TrieNodeID::Node256, 0x14,
            TrieNodeID::Node256, 0x15,
            TrieNodeID::Node256, 0x16,
            TrieNodeID::Node256, 0x17,
            TrieNodeID::Node256, 0x18,
            TrieNodeID::Node256, 0x19,
            TrieNodeID::Node256, 0x1a,
            TrieNodeID::Node256, 0x1b,
            TrieNodeID::Node256, 0x1c,
            TrieNodeID::Node256, 0x1d,
            TrieNodeID::Node256, 0x1e,
            TrieNodeID::Node256, 0x1f,
            TrieNodeID::Node256, 0x20,
            TrieNodeID::Node256, 0x21,
            TrieNodeID::Node256, 0x22,
            TrieNodeID::Node256, 0x23,
            TrieNodeID::Node256, 0x24,
            TrieNodeID::Node256, 0x25,
            TrieNodeID::Node256, 0x26,
            TrieNodeID::Node256, 0x27,
            TrieNodeID::Node256, 0x28,
            TrieNodeID::Node256, 0x29,
            TrieNodeID::Node256, 0x2a,
            TrieNodeID::Node256, 0x2b,
            TrieNodeID::Node256, 0x2c, 
            TrieNodeID::Node256, 0x2d,
            TrieNodeID::Node256, 0x2e,
            TrieNodeID::Node256, 0x2f,
            TrieNodeID::Empty, 0x00,
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
        assert_eq!(node48.to_consensus_bytes(), node48_bytes);
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
                TrieNodeID::Node256, i as u8, 0, 0, 0, 0, 0, 0, 0, ((i+2) % 256) as u8
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

        assert_eq!(node256.to_bytes(), node256_bytes);
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
                TrieNodeID::Node256, i as u8
            ]);
        }
        // last ptr is empty 
        node256_bytes.append(&mut vec![
            TrieNodeID::Empty, 0
        ]);
        // path 
        node256_bytes.append(&mut vec![
            // path len
            0x14,
            // path 
            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10, 0x11, 0x12, 0x13
        ]);

        let node256_stream = Cursor::new(node256_bytes.clone());

        assert_eq!(node256.to_consensus_bytes(), node256_bytes);
    }

    #[test]
    fn trie_leaf_to_bytes() {
        let leaf = TrieLeaf::new(&vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19], &vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39]);
        let leaf_bytes = leaf.to_bytes();

        assert_eq!(leaf_bytes,
                   vec![
                        // node ID
                        TrieNodeID::Leaf,
                        // path len
                        0x14,
                        // path
                        0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,
                        // reserved
                        0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39
                    ]);
    }
    
    #[test]
    fn trie_leaf_to_consensus_bytes() {
        let leaf = TrieLeaf::new(&vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19], &vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39]);
        let leaf_bytes = leaf.to_consensus_bytes();

        assert_eq!(leaf_bytes,
                   vec![
                        // node ID
                        TrieNodeID::Leaf,
                        // path len
                        0x14,
                        // path
                        0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,
                        // reserved
                        0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39
                    ]);
    }

    #[test]
    fn trie_backptr_to_bytes() {
        let backptr = TrieBackPtr::new(&BlockHeaderHash::from_bytes(&[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]).unwrap(), &TriePtr::new(TrieNodeID::Node256, 32, 33));
        let backptr_bytes = backptr.to_bytes();

        assert_eq!(backptr_bytes,
                   vec![
                        // node ID 
                        TrieNodeID::BackPtr,
                        // ptrs (1)
                        TrieNodeID::Node256, 32, 0, 0, 0, 0, 0, 0, 0, 33,
                        // header hash
                        0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31
                    ]);
    }

    #[test]
    fn trie_backptr_to_consensus_bytes() {
        let backptr = TrieBackPtr::new(&BlockHeaderHash::from_bytes(&[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]).unwrap(), &TriePtr::new(TrieNodeID::Node256, 32, 33));
        let backptr_bytes = backptr.to_consensus_bytes();

        assert_eq!(backptr_bytes,
                   vec![
                        // node ID 
                        TrieNodeID::BackPtr,
                        // ptrs (1)
                        TrieNodeID::Node256, 32,
                        // block header hash
                        0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31
                    ]);
    }

    #[test]
    fn read_write_node4() {
        let mut node4 = TrieNode4::new(&vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19]);
        for i in 0..3 {
            assert!(node4.insert(&TriePtr::new(TrieNodeID::Node16, (i+1) as u8, (i+2) as u64)));
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
            assert!(node16.insert(&TriePtr::new(TrieNodeID::Node48, (i+1) as u8, (i+2) as u64)));
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
            assert!(node48.insert(&TriePtr::new(TrieNodeID::Node256, (i+1) as u8, (i+2) as u64)));
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
            assert!(node256.insert(&TriePtr::new(TrieNodeID::Node256, (i+1) as u8, (i+2) as u64)));
        }
        let f = Cursor::new(vec![]);
        let mut cursor = TrieIOBuffer::new(f);
        let hash = TrieHash::from_data(&[0u8; 32]);
        let wres = Trie::write_nodetype(&mut cursor, &TrieNodeType::Node256(node256.clone()), hash.clone());
        assert!(wres.is_ok());

        fseek(&mut cursor, 0).unwrap();
        let rres = Trie::read_node(&mut cursor, &TriePtr::new(TrieNodeID::Node256, 0, 0));
        
        assert!(rres.is_ok());
        assert_eq!(rres.unwrap(), (TrieNodeType::Node256(node256.clone()), hash));
    }

    #[test]
    fn read_write_leaf() {
        let leaf = TrieLeaf::new(&vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19], &vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39]);

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
    fn read_write_backptr() {
        let backptr = TrieBackPtr::new(&BlockHeaderHash::from_bytes(&[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]).unwrap(), &TriePtr::new(TrieNodeID::Node256, 32, 33));

        let f = Cursor::new(vec![]);
        let mut cursor = TrieIOBuffer::new(f);
        let hash = TrieHash::from_data(&[0u8; 32]);
        let wres = Trie::write_nodetype(&mut cursor, &TrieNodeType::BackPtr(backptr.clone()), hash.clone());
        assert!(wres.is_ok());

        fseek(&mut cursor, 0).unwrap();
        let rres = Trie::read_node(&mut cursor, &TriePtr::new(TrieNodeID::BackPtr, 0, 0));
        
        assert!(rres.is_ok());
        assert_eq!(rres.unwrap(), (TrieNodeType::BackPtr(backptr.clone()), hash));
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
            assert!(node4.insert(&TriePtr::new(TrieNodeID::Leaf, i as u8, ptr as u64)));
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
            assert!(node16.insert(&TriePtr::new(TrieNodeID::Leaf, i as u8, ptr as u64)));
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
            assert!(node48.insert(&TriePtr::new(TrieNodeID::Leaf, i as u8, ptr as u64)));
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
            assert!(node256.insert(&TriePtr::new(TrieNodeID::Leaf, i as u8, ptr as u64)));
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
        fseek(s, 0).unwrap();
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
                TrieNodeType::Node256(ref mut data) => assert!(data.insert(&TriePtr::new(node_id, chr, node_ptr as u64))),
                TrieNodeType::Node48(ref mut data) => assert!(data.insert(&TriePtr::new(node_id, chr, node_ptr as u64))),
                TrieNodeType::Node16(ref mut data) => assert!(data.insert(&TriePtr::new(node_id, chr, node_ptr as u64))),
                TrieNodeType::Node4(ref mut data) => assert!(data.insert(&TriePtr::new(node_id, chr, node_ptr as u64))),
                TrieNodeType::Leaf(ref mut data) => panic!("can't insert into leaf"),
                TrieNodeType::BackPtr(ref mut data) => panic!("can't insert into backptr"),
            };

            Trie::write_nodetype(s, &parent, TrieHash::from_data(&[seg_id as u8; 32])).unwrap();
            
            fseek(s, sav).unwrap();
            
            nodes.push(parent.clone());
            node_ptrs.push(TriePtr::new(node_id, chr, node_ptr as u64));
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
            TrieNodeType::Node256(ref mut data) => assert!(data.insert(&TriePtr::new(TrieNodeID::Leaf, child_chr, child_ptr))),
            TrieNodeType::Node48(ref mut data) => assert!(data.insert(&TriePtr::new(TrieNodeID::Leaf, child_chr, child_ptr))),
            TrieNodeType::Node16(ref mut data) => assert!(data.insert(&TriePtr::new(TrieNodeID::Leaf, child_chr, child_ptr))),
            TrieNodeType::Node4(ref mut data) => assert!(data.insert(&TriePtr::new(TrieNodeID::Leaf, child_chr, child_ptr))),
            TrieNodeType::Leaf(ref mut data) => panic!("can't insert into leaf"),
            TrieNodeType::BackPtr(ref mut data) => panic!("can't insert into backptr")
        };

        Trie::write_nodetype(s, &parent, TrieHash::from_data(&[(seg_id) as u8; 32])).unwrap();

        fseek(s, sav).unwrap();

        nodes.push(parent.clone());
        node_ptrs.push(TriePtr::new(TrieNodeID::Leaf, child_chr, child_ptr as u64));
        hashes.push(TrieHash::from_data(&[(seg_id+1) as u8; 32]));

        fseek(s, 0).unwrap();
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
        let mut c = TrieCursor::new(&TriePath::from_bytes(&path).unwrap());
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
        let mut c = TrieCursor::new(&TriePath::from_bytes(&path).unwrap());
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
        let mut c = TrieCursor::new(&TriePath::from_bytes(&path).unwrap());
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
        let mut c = TrieCursor::new(&TriePath::from_bytes(&path).unwrap());
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
        let mut c = TrieCursor::new(&TriePath::from_bytes(&path).unwrap());
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
        let mut c = TrieCursor::new(&TriePath::from_bytes(&path).unwrap());
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
        let mut c = TrieCursor::new(&TriePath::from_bytes(&path).unwrap());
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
        let mut c = TrieCursor::new(&TriePath::from_bytes(&path).unwrap());
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
        let mut c = TrieCursor::new(&TriePath::from_bytes(&path).unwrap());
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

                let mut c = TrieCursor::new(&TriePath::from_bytes(&path[..]).unwrap());
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
        let mut c = TrieCursor::new(&TriePath::from_bytes(&[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19]).unwrap());

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

            let mut c = TrieCursor::new(&TriePath::from_bytes(&path[..]).unwrap());
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

                        fseek(&mut f, node_ptr.ptr()).unwrap();
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

                let mut c = TrieCursor::new(&TriePath::from_bytes(&path[..]).unwrap());
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

            let mut c = TrieCursor::new(&TriePath::from_bytes(&path[..]).unwrap());
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

                let mut c = TrieCursor::new(&TriePath::from_bytes(&path[..]).unwrap());
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

            let mut c = TrieCursor::new(&TriePath::from_bytes(&path[..]).unwrap());
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

                let mut c = TrieCursor::new(&TriePath::from_bytes(&path[..]).unwrap());
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

            let mut c = TrieCursor::new(&TriePath::from_bytes(&path[..]).unwrap());
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

                let mut c = TrieCursor::new(&TriePath::from_bytes(&path[..]).unwrap());
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

            let mut c = TrieCursor::new(&TriePath::from_bytes(&path[..]).unwrap());
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

                let mut c = TrieCursor::new(&TriePath::from_bytes(&path[..]).unwrap());
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

            let mut c = TrieCursor::new(&TriePath::from_bytes(&path[..]).unwrap());
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

                let mut c = TrieCursor::new(&TriePath::from_bytes(&path[..]).unwrap());
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

            let mut c = TrieCursor::new(&TriePath::from_bytes(&path[..]).unwrap());
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

                let mut c = TrieCursor::new(&TriePath::from_bytes(&path[..]).unwrap());
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

                let mut c = TrieCursor::new(&TriePath::from_bytes(&path[..]).unwrap());
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

    /// Verify that all nodes along a path are _not_ BackPtrs.
    /// Return the TrieCursor from walking down the path
    fn marf_verify_cow<S: TrieStorage + Seek>(s: &mut S, block_header: &BlockHeaderHash, path: &Vec<u8>) -> TrieCursor {
        // walk to insertion point 
        s.open(block_header).unwrap();
        let (mut node, _) = Trie::read_root(s).unwrap();
        let mut node_ptr = TriePtr::new(0,0,0);

        let mut c = TrieCursor::new(&TriePath::from_bytes(&path[..]).unwrap());

        for _ in 0..c.path.len()+1 {
            let next_opt = Trie::walk_from(s, &node, &mut c).unwrap();
            match next_opt {
                Some((next_node_ptr, next_node, _)) => {
                    // keep walking 
                    node = next_node;
                    node_ptr = next_node_ptr;
                    continue;
                },
                None => {
                    match node {
                        TrieNodeType::BackPtr(ref backptr) => {
                            // backptr encountered!
                            assert!(false);
                        },
                        _ => {}
                    };
                }
            }
            if c.eop() {
                break;
            }
        }
        c
    }

    #[test]
    fn marf_walk_cow_node4_20() {
        let cursor = Cursor::new(vec![]);
        let mut f = TrieIOBuffer::new(cursor);

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

            f.open(&next_block_header).unwrap();

            test_debug!("----------------");
            test_debug!("MARF verify cow");
            test_debug!("----------------");

            // verify that all non-empty ptrs in all intermediate nodes are BackPtrs
            let c = marf_verify_cow(&mut f, &next_block_header, &next_path);
            let mut leaf_count = 0;
            let mut backptr_count = 0;
            for node in c.nodes.iter() {
                let ptrs = match node {
                    TrieNodeType::Node4(ref data) => data.ptrs.to_vec(),
                    TrieNodeType::Node16(ref data) => data.ptrs.to_vec(),
                    TrieNodeType::Node48(ref data) => data.ptrs.to_vec(),
                    TrieNodeType::Node256(ref data) => data.ptrs.to_vec(),
                    TrieNodeType::Leaf(_) => vec![],
                    _ => { assert!(false); vec![] }
                };
                for ptr in ptrs {
                    if ptr.id() == TrieNodeID::Leaf {
                        leaf_count += 1;
                    }
                    else if ptr.id() != TrieNodeID::Empty {
                        backptr_count += 1;
                    }
                }
            }

            dump_trie(&mut f);

            // only one leaf in this trie
            assert_eq!(leaf_count, 1);
            // assert_eq!(backptr_count, i-1);
            
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
        let cursor = Cursor::new(vec![]);
        let mut f = TrieIOBuffer::new(cursor);

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

            f.open(&next_block_header).unwrap();

            test_debug!("----------------");
            test_debug!("MARF verify cow");
            test_debug!("----------------");

            // verify that all non-empty ptrs in all intermediate nodes are BackPtrs
            let c = marf_verify_cow(&mut f, &next_block_header, &next_path);
            let mut leaf_count = 0;
            let mut backptr_count = 0;
            for node in c.nodes.iter() {
                let ptrs = match node {
                    TrieNodeType::Node4(ref data) => data.ptrs.to_vec(),
                    TrieNodeType::Node16(ref data) => data.ptrs.to_vec(),
                    TrieNodeType::Node48(ref data) => data.ptrs.to_vec(),
                    TrieNodeType::Node256(ref data) => data.ptrs.to_vec(),
                    TrieNodeType::Leaf(_) => vec![],
                    _ => { assert!(false); vec![] }
                };
                for ptr in ptrs {
                    if ptr.id() == TrieNodeID::Leaf {
                        leaf_count += 1;
                    }
                    else if ptr.id() != TrieNodeID::Empty {
                        backptr_count += 1;
                    }
                }
            }

            dump_trie(&mut f);

            // only one leaf in this trie
            assert_eq!(leaf_count, 1);
            // assert_eq!(backptr_count, i-1);
            
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

    // This test is just used for benchmarking -- it doesn't check anything
    #[test]
    fn insert_4096_TrieRAM_random() {
        let mut f = TrieRAM::new();

        let block_header = BlockHeaderHash::from_bytes(&[0u8; 32]).unwrap();
        MARF::format(&mut f, &block_header).unwrap();

        let mut seed = TrieHash::from_data(&[]).as_bytes().to_vec();

        for i in 0..4096 {
            let i0 = i / 256;
            let i1 = i % 256;
            let path = TrieHash::from_data(&seed[..]).as_bytes()[0..20].to_vec();
            seed = path.clone();
            
            let triepath = TriePath::from_bytes(&path[..]).unwrap();
            let value = TrieLeaf::new(&vec![], &[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,i0 as u8, i1 as u8].to_vec());
            MARF::insert(&mut f, &block_header, &triepath, &value).unwrap();
        }
    }
    
    // This test is just used for benchmarking -- it doesn't check anything
    #[test]
    fn insert_4096_TrieIOBuffer_random() {
        let cursor = Cursor::new(vec![]);
        let mut f = TrieIOBuffer::new(cursor);

        let block_header = BlockHeaderHash::from_bytes(&[0u8; 32]).unwrap();
        MARF::format(&mut f, &block_header).unwrap();
        
        let mut seed = TrieHash::from_data(&[]).as_bytes().to_vec();

        for i in 0..4096 {
            let i0 = i / 256;
            let i1 = i % 256;
            let path = TrieHash::from_data(&seed[..]).as_bytes()[0..20].to_vec();
            seed = path.clone();
            
            let triepath = TriePath::from_bytes(&path[..]).unwrap();
            let value = TrieLeaf::new(&vec![], &[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,i0 as u8, i1 as u8].to_vec());
            MARF::insert(&mut f, &block_header, &triepath, &value).unwrap();
        }
    }
    
    // This test is just used for benchmarking -- it doesn't check anything
    #[test]
    fn insert_4096_TrieRAM_seq_low() {
        let mut f = TrieRAM::new();

        let block_header = BlockHeaderHash::from_bytes(&[0u8; 32]).unwrap();
        MARF::format(&mut f, &block_header).unwrap();

        for i in 0..4096 {
            let i0 = i / 256;
            let i1 = i % 256;
            let path = [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,i0 as u8, i1 as u8];
            let triepath = TriePath::from_bytes(&path[..]).unwrap();

            let value = TrieLeaf::new(&vec![], &[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,i0 as u8, i1 as u8].to_vec());
            MARF::insert(&mut f, &block_header, &triepath, &value).unwrap();
        }
    }
    
    // This test is just used for benchmarking -- it doesn't check anything
    #[test]
    fn insert_4096_TrieIOBuffer_seq_low() {
        let cursor = Cursor::new(vec![]);
        let mut f = TrieIOBuffer::new(cursor);

        let block_header = BlockHeaderHash::from_bytes(&[0u8; 32]).unwrap();
        MARF::format(&mut f, &block_header).unwrap();

        for i in 0..4096 {
            let i0 = i / 256;
            let i1 = i % 256;
            let path = [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,i0 as u8, i1 as u8];

            let triepath = TriePath::from_bytes(&path[..]).unwrap(); 
            let value = TrieLeaf::new(&vec![], &[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,i0 as u8, i1 as u8].to_vec());
            MARF::insert(&mut f, &block_header, &triepath, &value).unwrap();
        }
    }
}
