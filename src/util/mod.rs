use std::fmt;
use std::error;
use std::io;
use std::io::{
    Read,
    Write,
    Seek,
    SeekFrom
};

use std::char::from_digit;
use std::marker::PhantomData;

use sha2::Sha256;
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
            eprintln!($($arg)*);
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

pub struct DoubleSha256(pub [u8; 32]);
impl_array_newtype!(DoubleSha256, u8, 32);
impl_array_hexstring_fmt!(DoubleSha256);
impl_byte_array_newtype!(DoubleSha256, u8, 32);

impl DoubleSha256 {
    pub fn from_data(data: &[u8]) -> DoubleSha256 {
        use sha2::Digest;
        let mut tmp = [0u8; 32];
        
        let mut sha2 = Sha256::new();
        sha2.input(data);
        tmp.copy_from_slice(sha2.result().as_slice());

        let mut sha2_2 = Sha256::new();
        sha2_2.input(&tmp);
        tmp.copy_from_slice(sha2_2.result().as_slice());

        DoubleSha256(tmp)
    }

    pub fn from_sha256(h: [u8; 32]) -> DoubleSha256 {
        use sha2::Digest;
        
        let mut tmp = [0u8; 32];
        let mut sha2_2 = Sha256::new();
        sha2_2.input(&h);
        tmp.copy_from_slice(sha2_2.result().as_slice());

        DoubleSha256(tmp)
    }

    /// Human-readable hex output
    pub fn le_hex_string(&self) -> String {
        let &DoubleSha256(data) = self;
        let mut ret = String::with_capacity(64);
        for item in data.iter().take(32) {
            ret.push(from_digit((*item / 0x10) as u32, 16).unwrap());
            ret.push(from_digit((*item & 0x0f) as u32, 16).unwrap());
        }
        ret
    }

    /// Human-readable hex output
    pub fn be_hex_string(&self) -> String {
        let &DoubleSha256(data) = self;
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
    FilesystemError(io::Error),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Error::FilesystemError(ref e) => fmt::Display::fmt(e, f),
        }
    }
}

impl error::Error for Error {
    fn cause(&self) -> Option<&error::Error> {
        match *self {
            Error::FilesystemError(ref e) => Some(e),
        }
    }

    fn description(&self) -> &str {
        match *self {
            Error::FilesystemError(ref e) => e.description(),
        }
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

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

pub struct Trie<T: Read + Write + Seek> {
    pub path: String,
    pub _phantom: PhantomData<T>
}

pub mod TrieNodeID {
    pub const Empty : u8 = 0;
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
    node_ptrs: Vec<TriePtr>     // list of ptr branches this cursor has taken
}

impl TrieCursor {
    pub fn new(path: &TriePath) -> TrieCursor {
        TrieCursor {
            path: path.clone(),
            index: 0,
            node_path_index: 0,
            nodes: vec![],
            node_ptrs: vec![TriePtr::new(TrieNodeID::Node256, 0, 0)]
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
            TrieNodeType::Node256(ref data) => self.node_path_index == data.path.len()
        }
    }

    /// Replace the last-visited node and ptr
    pub fn retarget(&mut self, node: &TrieNodeType, ptr: &TriePtr) -> () {
        self.nodes.pop();
        self.node_ptrs.pop();

        self.nodes.push(node.clone());
        self.node_ptrs.push(ptr.clone());
    }

    pub fn walk(&mut self, node: &TrieNodeType) -> Option<TriePtr> {
        test_debug!("cursor: walk: node = {:?}", node);
        if self.index >= self.path.len() {
            test_debug!("cursor: out of path");
            return None;
        }

        let node_path = match node {
            TrieNodeType::Leaf(ref data) => data.path.clone(),
            TrieNodeType::Node4(ref data) => data.path.clone(),
            TrieNodeType::Node16(ref data) => data.path.clone(),
            TrieNodeType::Node48(ref data) => data.path.clone(),
            TrieNodeType::Node256(ref data) => data.path.clone()
        };

        let path_bytes = self.path.as_bytes();

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
                Some(ref ptr) => self.node_ptrs.push(ptr.clone()),
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

fn ftell<F: Seek>(f: &mut F) -> Result<u64, Error> {
    f.seek(SeekFrom::Current(0))
        .map_err(Error::FilesystemError)
}

fn fsize<F: Seek>(f: &mut F) -> Result<u64, Error> {
    let prev = ftell(f)?;
    let res = f.seek(SeekFrom::End(0))
        .map_err(Error::FilesystemError)?;
    f.seek(SeekFrom::Start(prev))
        .map_err(Error::FilesystemError)?;
    Ok(res)
}

fn fseek<F: Seek>(f: &mut F, off: u64) -> Result<u64, Error> {
    f.seek(SeekFrom::Start(off))
        .map_err(Error::FilesystemError)
}

fn fseek_end<F: Seek>(f: &mut F) -> Result<u64, Error> {
    f.seek(SeekFrom::End(0))
        .map_err(Error::FilesystemError)
}

fn read_all<R: Read>(f: &mut R, buf: &mut [u8]) -> Result<usize, Error> {
    let mut cnt = 0;
    while cnt < buf.len() {
        let nr = f.read(&mut buf[cnt..])
            .map_err(Error::FilesystemError)?;

        if nr == 0 {
            break;
        }

        cnt += nr;
    }
    Ok(cnt)
}

fn path_to_bytes(p: &Vec<u8>) -> Vec<u8> {
    assert!(p.len() < 256);
    let mut ret = Vec::with_capacity(p.len() + 1);
    ret.push(p.len() as u8);
    ret.append(&mut p.clone());
    ret
}

fn path_from_bytes<R: Read>(r: &mut R) -> Result<Vec<u8>, Error> {
    let mut lenbuf = [0u8; 1];
    let l_lenbuf = read_all(r, &mut lenbuf)?;

    assert!(l_lenbuf == 1);

    let mut retbuf = vec![0; lenbuf[0] as usize];
    let l_retbuf = read_all(r, &mut retbuf)?;

    assert!(l_retbuf == lenbuf[0] as usize);
    Ok(retbuf)
}

fn check_node_id(node_id: u8) -> bool {
    node_id == TrieNodeID::Leaf ||
    node_id == TrieNodeID::Node4 ||
    node_id == TrieNodeID::Node16 ||
    node_id == TrieNodeID::Node48 ||
    node_id == TrieNodeID::Node256
}

fn node_id_to_ptr_count(node_id: u8) -> usize {
    match node_id {
        TrieNodeID::Leaf => 0,
        TrieNodeID::Node4 => 4,
        TrieNodeID::Node16 => 16,
        TrieNodeID::Node48 => 48,
        TrieNodeID::Node256 => 256,
        _ => panic!("Unknown node ID {}", node_id)
    }
}

fn ptrs_to_bytes(node_id: u8, ptrs: &[TriePtr]) -> Vec<u8> {
    assert!(check_node_id(node_id));
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
    assert!(check_node_id(node_id));

    let mut idbuf = [0u8; 1];
    let l_idbuf = read_all(r, &mut idbuf)?;

    assert!(l_idbuf == 1);
    assert!(idbuf[0] == node_id);

    let num_ptrs = node_id_to_ptr_count(node_id);
    let mut bytes = vec![0; num_ptrs * TRIEPTR_SIZE];
    let l_bytes = read_all(r, &mut bytes)?;

    assert!(l_bytes == num_ptrs * TRIEPTR_SIZE);
    
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
            .map_err(Error::FilesystemError)?;
        
        assert!(l_indexes == 256);

        let path = path_from_bytes(r)?;

        let mut ptrs_slice = [TriePtr::default(); 48];
        ptrs_slice.copy_from_slice(&ptrs[..]);

        let indexes_i8 : Vec<i8> = indexes.iter().map(|i| { let j = *i as i8; j } ).collect();
        let mut indexes_slice = [0i8; 256];
        indexes_slice.copy_from_slice(&indexes_i8[..]);

        for ptr in ptrs_slice.iter() {
            assert!(ptr.id() == TrieNodeID::Empty || (indexes_slice[ptr.chr() as usize] >= 0 && indexes_slice[ptr.chr() as usize] < 48));
        }
        for i in 0..256 {
            assert!(indexes_slice[i] < 0 || (indexes_slice[i] >= 0 && (indexes_slice[i] as usize) < ptrs_slice.len() && ptrs_slice[indexes_slice[i] as usize].id() != TrieNodeID::Empty));
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
            .map_err(Error::FilesystemError)?;

        assert!(l_reserved == 40);
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
}

#[derive(Debug, Clone, PartialEq)]
pub enum TrieNodeType {
    Node4(TrieNode4),
    Node16(TrieNode16),
    Node48(TrieNode48),
    Node256(TrieNode256),
    Leaf(TrieLeaf)
}

impl<F> Trie<F>
where
    F: Read + Write + Seek
{
    pub fn format(f: &mut F) -> Result<(), Error> {
        // format the given FD
        // write an empty root 
        let root_node = TrieNode256::empty();
        let root_hash = DoubleSha256::from_data(&[]);

        fseek(f, 0)?;
        Trie::write_node(f, &root_node, root_hash)
            .and_then(|_| Ok(()))
    }

    fn read_root(f: &mut F) -> Result<(TrieNodeType, DoubleSha256), Error> {
        fseek(f, 0)?;
        Trie::read_node(f, &TriePtr::new(TrieNodeID::Node256, 0, 0))
    }

    fn root_ptr() -> TriePtr {
        TriePtr::new(TrieNodeID::Node256, 0, 0)
    }

    fn read_hash(f: &mut F) -> Result<DoubleSha256, Error> {
        let mut hashbytes = [0u8; 32];
        f.read(&mut hashbytes)
            .map_err(Error::FilesystemError)?;
        Ok(DoubleSha256(hashbytes))
    }

    fn read_node_hash(f: &mut F, ptr: &TriePtr) -> Result<DoubleSha256, Error> {
        fseek(f, ptr.ptr())?;
        Trie::read_hash(f)
    }

    /// Node wire format:
    /// 0               32 33               33+X         33+X+Y
    /// |---------------|--|------------------|-----------|
    ///   node hash      id  ptrs & ptr data      path
    ///
    /// X is fixed and determined by the TrieNodeType variant.
    /// Y is variable, but no more than TriePath::len()
    fn read_node(f: &mut F, ptr: &TriePtr) -> Result<(TrieNodeType, DoubleSha256), Error> {
        test_debug!("read_node at {:?}", ptr);
        let h = Trie::read_node_hash(f, ptr)?;
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
            _ => panic!("Unknown node ID {}", ptr.id())
        };

        Ok((node, h))
    }
    
    /// write all the bytes for a node, including its hash
    fn write_node<T: TrieNode + std::fmt::Debug>(f: &mut F, node: &T, hash: DoubleSha256) -> Result<usize, Error> {
        let mut cnt = 0;
        let mut bytes = hash.as_bytes().to_vec();
        let mut node_bytes = node.to_bytes();

        bytes.append(&mut node_bytes);

        let ptr = ftell(f)?;
        test_debug!("write_node: {:?} at {}-{}", node, ptr, ptr + bytes.len() as u64);

        while cnt < bytes.len() {
            let nw = f.write(&bytes[cnt..bytes.len()])
                .map_err(Error::FilesystemError)?;
            cnt += nw;
        }
        
        Ok(cnt)
    }

    /// write a node from its type variant
    fn write_nodetype(f: &mut F, node: &TrieNodeType, hash: DoubleSha256) -> Result<usize, Error> {
        match node {
            TrieNodeType::Leaf(ref data) => Trie::write_node(f, data, hash),
            TrieNodeType::Node4(ref data) => Trie::write_node(f, data, hash),
            TrieNodeType::Node16(ref data) => Trie::write_node(f, data, hash),
            TrieNodeType::Node48(ref data) => Trie::write_node(f, data, hash),
            TrieNodeType::Node256(ref data) => Trie::write_node(f, data, hash),
        }
    }
     
    /// Walk from the given node to the next node on the path, advancing the cursor.
    /// Return the TriePtr followed, the _next_ node to walk, and the hash of the _current_ node.
    /// Returns None if we either didn't find the node, or we're out of path, or we're at a leaf.
    fn walk_from(f: &mut F, node: &TrieNodeType, c: &mut TrieCursor) -> Result<Option<(TriePtr, TrieNodeType, DoubleSha256)>, Error> {
        let ptr_opt = c.walk(node);
        match ptr_opt {
            None => {
                Ok(None)
            },
            Some(ptr) => {
                let (node, hash) = Trie::read_node(f, &ptr)?;
                Ok(Some((ptr, node, hash)))
            }
        }
    }

    pub fn get(f: &mut F, path: &TriePath) -> Result<Option<TrieLeaf>, Error> {
        test_debug!("Get {:?}", path);
        let mut c = TrieCursor::new(path);
        let (mut node, root_hash) = Trie::read_root(f)?;
        for _ in 0..c.path.len()+1 {
            test_debug!("get: at {:?} on {:?}", &node, path);
            let next_opt = Trie::walk_from(f, &node, &mut c)?;
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

    fn read_node_hashes(f: &mut F, ptrs: &[TriePtr]) -> Result<Vec<DoubleSha256>, Error> {
        let mut ret = vec![];
        for i in 0..ptrs.len() {
            if ptrs[i].id() == TrieNodeID::Empty {
                // double-sha256 hash of empty string
                ret.push(DoubleSha256::from_data(&[]));
            }
            else {
                let h = Trie::read_node_hash(f, &ptrs[i])?;
                ret.push(h);
            }
        }
        Ok(ret)
    }

    fn get_children_hashes(f: &mut F, node: &TrieNodeType) -> Result<Vec<DoubleSha256>, Error> {
        match node {
            TrieNodeType::Leaf(_) => {
                Ok(vec![])
            },
            TrieNodeType::Node4(ref data) => {
                let ret = Trie::read_node_hashes(f, &data.ptrs)?;
                Ok(ret)
            },
            TrieNodeType::Node16(ref data) => {
                let ret = Trie::read_node_hashes(f, &data.ptrs)?;
                Ok(ret)
            },
            TrieNodeType::Node48(ref data) => {
                let ret = Trie::read_node_hashes(f, &data.ptrs)?;
                Ok(ret)
            },
            TrieNodeType::Node256(ref data) => {
                let ret = Trie::read_node_hashes(f, &data.ptrs)?;
                Ok(ret)
            }
        }
    }

    /// hash this node and its childrens' hashes
    fn get_node_hash<T: TrieNode>(node: &T, child_hashes: &Vec<DoubleSha256>) -> DoubleSha256 {
        let mut sha2 = Sha256::new();
        sha2.input(&node.to_consensus_bytes()[..]);
        for child_hash in child_hashes {
            sha2.input(&child_hash.as_bytes());
        }
        
        let mut res = [0u8; 32];
        res.copy_from_slice(sha2.result().as_slice());

        DoubleSha256::from_sha256(res)
    }

    /// Given a leaf, replace it.
    /// c must point to the value to replace
    fn replace_leaf(f: &mut F, c: &TrieCursor, value: &TrieLeaf) -> Result<TriePtr, Error> {
        let leaf_hash = Trie::<F>::get_node_hash(value, &vec![]);
        fseek(f, c.ptr().ptr())?;
        Trie::write_node(f, value, leaf_hash.clone())?;
        Ok(c.ptr())
    }

    /// Append a leaf to the trie, and return the TriePtr to it.
    /// Do lazy expansion -- have the leaf store the trailing path to it.
    /// Return the TriePtr to the newly-written leaf
    fn append_leaf(f: &mut F, c: &TrieCursor, value: &mut TrieLeaf) -> Result<TriePtr, Error> {
        assert!(c.chr().is_some());

        let ptr = fseek_end(f)?;
        let chr = c.chr().unwrap();
        let leaf_path = &c.path.as_bytes()[c.index..];

        value.path = leaf_path.to_vec();
        let leaf_hash = Trie::<F>::get_node_hash(value, &vec![]);

        Trie::write_node(f, value, leaf_hash)?;
       
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
    fn promote_leaf_to_node4(f: &mut F, c: &mut TrieCursor, cur_leaf_data: &mut TrieLeaf, new_leaf_data: &mut TrieLeaf) -> Result<TriePtr, Error> {
        // can only work if we're not at the end of the path, and the current node has a path
        assert!(!c.eop());
        assert!(cur_leaf_data.path.len() > 0);

        // switch from lazy expansion to path compression --
        // * the current and new leaves will have unique suffixes
        // * the node4 will have their shared prefix
        let cur_leaf_ptr = c.ptr();
        let node4_path = cur_leaf_data.path[0..(if c.ntell() == 0 { 0 } else { c.ntell() })].to_vec();
        let node4_chr = cur_leaf_ptr.chr();

        let cur_leaf_chr = cur_leaf_data.path[c.node_path_index];
        let cur_leaf_path = cur_leaf_data.path[(if c.ntell() >= cur_leaf_data.path.len() { c.ntell() } else { c.ntell() + 1 })..].to_vec();

        // update current leaf (path changed) and save it
        let cur_leaf_disk_ptr = ftell(f)?;
        let cur_leaf_new_ptr = TriePtr::new(TrieNodeID::Leaf, cur_leaf_chr, cur_leaf_disk_ptr);

        assert!(cur_leaf_path.len() <= cur_leaf_data.path.len());
        let sav_cur_leaf_data = cur_leaf_data.clone();
        cur_leaf_data.path = cur_leaf_path;
        let cur_leaf_hash = Trie::<F>::get_node_hash(cur_leaf_data, &vec![]);

        // NOTE: this is safe since the current leaf's byte representation has gotten shorter
        Trie::write_node(f, cur_leaf_data, cur_leaf_hash.clone())?;
        
        // append the new leaf and the end of the file.
        let new_leaf_disk_ptr = fseek_end(f)?;
        let new_leaf_chr = c.path[c.tell()];        // NOTE: this is safe because !c.eop()
        let new_leaf_path = c.path[(if c.tell()+1 <= c.path.len() { c.tell()+1 } else { c.path.len() })..].to_vec();
        let new_leaf_hash = Trie::<F>::get_node_hash(new_leaf_data, &vec![]);
        new_leaf_data.path = new_leaf_path;

        Trie::write_node(f, new_leaf_data, new_leaf_hash.clone())?;

        let new_leaf_ptr = TriePtr::new(TrieNodeID::Leaf, new_leaf_chr, new_leaf_disk_ptr);

        // append the Node4 that points to both of them, and put it after the new leaf
        let node4_disk_ptr = fseek_end(f)?;
        let mut node4_data = TrieNode4::new(&node4_path);

        assert!(node4_data.insert(&cur_leaf_new_ptr));
        assert!(node4_data.insert(&new_leaf_ptr));

        let node4_hash = Trie::<F>::get_node_hash(&node4_data, &vec![cur_leaf_hash, new_leaf_hash]);

        Trie::write_node(f, &node4_data, node4_hash.clone())?;

        let ret = TriePtr::new(TrieNodeID::Node4, node4_chr, node4_disk_ptr);
        c.retarget(&TrieNodeType::Node4(node4_data.clone()), &ret);

        test_debug!("Promoted {:?} to {:?}, {:?}, {:?}, new ptr = {:?}", sav_cur_leaf_data, cur_leaf_data, &node4_data, new_leaf_data, &ret);
        Ok(ret)
    }

    #[cfg(test)]
    fn count_children(children: &[TriePtr]) -> usize {
        let mut cnt = 0;
        for i in 0..children.len() {
            if children[i].id() != TrieNodeID::Empty {
                cnt += 1;
            }
        }
        cnt
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
    fn try_attach_leaf(f: &mut F, c: &TrieCursor, leaf: &mut TrieLeaf, node: &mut TrieNodeType) -> Result<Option<TriePtr>, Error> {
        // can only do this if we're at the end of the node's path
        if !c.eonp(node) {
            // nope
            return Ok(None);
        }
        assert!(c.chr().is_some());

        fn attach_leaf<T: TrieNode + fmt::Debug, F: Read + Write + Seek>(f: &mut F, c: &TrieCursor, leaf: &mut TrieLeaf, node_data: &mut T) -> Result<Option<TriePtr>, Error> {
            let has_space = Trie::<F>::node_has_space(c.chr().unwrap(), node_data.ptrs());
            if !has_space {
                // nope!
                return Ok(None);
            }
            // write leaf and update parent
            let leaf_ptr = Trie::append_leaf(f, c, leaf)?;
            let inserted = node_data.insert(&leaf_ptr);

            assert!(inserted);

            let node_hashes = Trie::read_node_hashes(f, node_data.ptrs())?;
            let new_node_hash = Trie::<F>::get_node_hash(node_data, &node_hashes);

            fseek(f, c.ptr().ptr())?;
            Trie::write_node(f, node_data, new_node_hash)?;

            Ok(Some(c.ptr()))
        }

        match node {
            TrieNodeType::Leaf(_) => panic!("Cannot insert into leaf"),
            TrieNodeType::Node4(ref mut data) => attach_leaf(f, c, leaf, data),
            TrieNodeType::Node16(ref mut data) => attach_leaf(f, c, leaf, data),
            TrieNodeType::Node48(ref mut data) => attach_leaf(f, c, leaf, data),
            TrieNodeType::Node256(ref mut data) => attach_leaf(f, c, leaf, data)
        }
    }

    /// Given a node and a leaf, attach the leaf.  Promote the intermediate node if necessary.
    /// Does the same thing as try_attach_leaf, but the node might get expanaded.  In this case, the
    /// new node will be appended and the old node will be leaked.
    fn insert_leaf(f: &mut F, c: &mut TrieCursor, leaf: &mut TrieLeaf, node: &mut TrieNodeType) -> Result<TriePtr, Error> {
        // can only do this if we're at the end of the node's path
        assert!(c.eonp(node));
        // assert!(!c.eop());

        let res = Trie::try_attach_leaf(f, c, leaf, node)?;
        if res.is_some() {
            // success!
            return Ok(res.unwrap());
        }

        fn inner_insert_leaf<T: TrieNode + fmt::Debug, F: Read + Write + Seek>(f: &mut F, c: &TrieCursor, leaf: &mut TrieLeaf, new_node_data: &mut T) -> Result<TriePtr, Error> {
            let node_ptr = c.ptr();
            let leaf_ptr = Trie::append_leaf(f, c, leaf)?;
            let inserted = new_node_data.insert(&leaf_ptr);
            assert!(inserted);
        
            let node_hashes = Trie::read_node_hashes(f, new_node_data.ptrs())?;
            let new_node_hash = Trie::<F>::get_node_hash(new_node_data, &node_hashes);

            let new_node_disk_ptr = fseek_end(f)?;
            Trie::write_node(f, new_node_data, new_node_hash.clone())?;
            
            // give back the promoted node's ptr
            Ok(TriePtr::new(new_node_data.id(), node_ptr.chr(), new_node_disk_ptr))
        }

        // need to promote node 
        match node {
            TrieNodeType::Leaf(_) => panic!("Cannot insert into a leaf"),
            TrieNodeType::Node4(ref data) => {
                let mut new_node = TrieNode16::from_node4(data);
                let ret = inner_insert_leaf(f, c, leaf, &mut new_node)?;
                c.retarget(&TrieNodeType::Node16(new_node), &ret);
                Ok(ret)
            },
            TrieNodeType::Node16(ref data) => {
                let mut new_node = TrieNode48::from_node16(data);
                let ret = inner_insert_leaf(f, c, leaf, &mut new_node)?;
                c.retarget(&TrieNodeType::Node48(new_node), &ret);
                Ok(ret)
            },
            TrieNodeType::Node48(ref data) => {
                let mut new_node = TrieNode256::from_node48(data);
                let ret = inner_insert_leaf(f, c, leaf, &mut new_node)?;
                c.retarget(&TrieNodeType::Node256(new_node), &ret);
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
    fn splice_leaf(f: &mut F, c: &mut TrieCursor, leaf: &mut TrieLeaf, node: &mut TrieNodeType) -> Result<TriePtr, Error> {
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
        let leaf_disk_ptr = fseek_end(f)?;
        let leaf_hash = Trie::<F>::get_node_hash(leaf, &vec![]);
        let leaf_ptr = TriePtr::new(TrieNodeID::Leaf, leaf_chr, leaf_disk_ptr);
        Trie::write_node(f, leaf, leaf_hash.clone())?;
       
        // update current node (node-X) and make a new path and ptr for it
        let cur_node_cur_ptr = c.ptr();
        let new_cur_node_disk_ptr = fseek_end(f)?;
        let new_cur_node_ptr = TriePtr::new(cur_node_cur_ptr.id(), new_cur_node_chr, new_cur_node_disk_ptr);

        fseek(f, cur_node_cur_ptr.ptr())?;
        let node_hashes = Trie::get_children_hashes(f, node)?;
        let new_cur_node_hash = match node {
            TrieNodeType::Leaf(_) => panic!("Intermediate node should not be a leaf"),
            TrieNodeType::Node4(ref mut data) => {
                data.path = new_cur_node_path;
                Trie::<F>::get_node_hash(data, &node_hashes)
            },
            TrieNodeType::Node16(ref mut data) => {
                data.path = new_cur_node_path;
                Trie::<F>::get_node_hash(data, &node_hashes)
            },
            TrieNodeType::Node48(ref mut data) => {
                data.path = new_cur_node_path;
                Trie::<F>::get_node_hash(data, &node_hashes)
            },
            TrieNodeType::Node256(ref mut data) => {
                data.path = new_cur_node_path;
                Trie::<F>::get_node_hash(data, &node_hashes)
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
                let new_node_hash = Trie::<F>::get_node_hash(&new_node, &vec![leaf_hash, new_cur_node_hash]);
                (TrieNodeID::Node4, TrieNodeType::Node4(new_node), new_node_hash)
            },
            TrieNodeType::Node16(_) => {
                let mut new_node = TrieNode16::new(&shared_path_prefix);
                new_node.insert(&leaf_ptr);
                new_node.insert(&new_cur_node_ptr);
                let new_node_hash = Trie::<F>::get_node_hash(&new_node, &vec![leaf_hash, new_cur_node_hash]);
                (TrieNodeID::Node16, TrieNodeType::Node16(new_node), new_node_hash)
            },
            TrieNodeType::Node48(_) => {
                let mut new_node = TrieNode48::new(&shared_path_prefix);
                new_node.insert(&leaf_ptr);
                new_node.insert(&new_cur_node_ptr);
                let new_node_hash = Trie::<F>::get_node_hash(&new_node, &vec![leaf_hash, new_cur_node_hash]);
                (TrieNodeID::Node48, TrieNodeType::Node48(new_node), new_node_hash)
            },
            TrieNodeType::Node256(_) => {
                let mut new_node = TrieNode256::new(&shared_path_prefix);
                new_node.insert(&leaf_ptr);
                new_node.insert(&new_cur_node_ptr);
                let new_node_hash = Trie::<F>::get_node_hash(&new_node, &vec![leaf_hash, new_cur_node_hash]);
                (TrieNodeID::Node256, TrieNodeType::Node256(new_node), new_node_hash)
            }
        };

        // store node-X' where node-X used to be
        fseek(f, cur_node_cur_ptr.ptr())?;
        Trie::write_nodetype(f, &new_node, new_node_hash.clone())?;

        // store node-X at the end
        fseek(f, new_cur_node_disk_ptr)?;
        Trie::write_nodetype(f, node, new_cur_node_hash.clone())?;

        let ret = TriePtr::new(new_node_id, cur_node_cur_ptr.chr(), cur_node_cur_ptr.ptr());
        c.retarget(&new_node.clone(), &ret);

        test_debug!("splice_leaf: node-X' at {:?}", &ret);
        Ok(ret)
    }

    /// Add a new value to the Trie at the location pointed at by the cursor.
    /// Returns a ptr to be inserted into the last node visited by the cursor.
    fn add_value(f: &mut F, c: &mut TrieCursor, value: &mut TrieLeaf) -> Result<TriePtr, Error> {
        let mut node = match c.node() {
            Some(n) => n,
            None => panic!("Cursor is uninitialized")
        };

        if c.eop() {
            match node {
                TrieNodeType::Leaf(_) => {
                    return Trie::replace_leaf(f, c, value);
                },
                _ => {}
            };

            Trie::insert_leaf(f, c, value, &mut node)
        }
        else {
            // didn't reach the end of the path, so we're on an intermediate node
            // or we're somewhere in the path of a leaf.
            // Either tack the leaf on (possibly promoting the node), or splice the leaf in.
            if c.eonp(&node) {
                Trie::insert_leaf(f, c, value, &mut node)
            }
            else {
                match node {
                    TrieNodeType::Leaf(ref mut data) => {
                        Trie::promote_leaf_to_node4(f, c, data, value)
                    },
                    _ => {
                        Trie::splice_leaf(f, c, value, &mut node)
                    }
                }
            }
        }
    }

    /// Unwind a TrieCursor to update the Merkle root of the trie.
    pub fn update_root_hash(f: &mut F, c: &TrieCursor) -> Result<(), Error> {
        assert!(c.node_ptrs.len() > 0);

        let mut ptrs = c.node_ptrs.clone();
        let mut child_ptr = ptrs.pop().unwrap();
        
        while ptrs.len() > 0 {
            let ptr = match ptrs.pop() {
                Some(p) => p,
                None => panic!("Out of ptrs")
            };
            let (mut node, _) = Trie::read_node(f, &ptr)?;

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

            test_debug!("Updated {:?} with {:?}", &node, &child_ptr);

            let hashes = Trie::get_children_hashes(f, &node)?;

            fseek(f, ptr.ptr())?;

            match node {
                TrieNodeType::Leaf(ref data) => Trie::write_node(f, data, Trie::<F>::get_node_hash(data, &hashes))?,
                TrieNodeType::Node4(ref data) => Trie::write_node(f, data, Trie::<F>::get_node_hash(data, &hashes))?,
                TrieNodeType::Node16(ref data) => Trie::write_node(f, data, Trie::<F>::get_node_hash(data, &hashes))?,
                TrieNodeType::Node48(ref data) => Trie::write_node(f, data, Trie::<F>::get_node_hash(data, &hashes))?,
                TrieNodeType::Node256(ref data) => Trie::write_node(f, data, Trie::<F>::get_node_hash(data, &hashes))?
            };

            child_ptr = ptr;
        }

        Ok(())
    }



    /// Try to insert a leaf after a node.
    /// If we passed through the end of this node's path,
    /// then if we have space to do so, insert the leaf.  Otherwise, promote the node.
    /// Otherwise, if we did _not_ pass through the end of the node's path,
    /// then split the path, add a Node4, and add this leaf and the current node as children.
    pub fn insert(f: &mut F, k: &TriePath, v: &TrieLeaf) -> Result<(), Error> {
        let mut value = v.clone();
        let mut c = TrieCursor::new(k);

        // walk to insertion point 
        let (mut node, root_hash) = Trie::read_root(f)?;
        let mut node_ptr = TriePtr::new(0,0,0);

        for _ in 0..c.path.len() {
            let next_opt = Trie::walk_from(f, &node, &mut c)?;
            match next_opt {
                Some((next_node_ptr, next_node, _next_node_hash)) => {
                    // keep walking
                    node = next_node;
                    node_ptr = next_node_ptr;
                    continue;
                },
                None => {
                    // end of path -- cursor points to the insertion point
                    fseek(f, node_ptr.ptr())?;
                    Trie::add_value(f, &mut c, &mut value)?;
                    Trie::update_root_hash(f, &c)?;
                    break;
                }
            }
        }
        
        Ok(())
    }
}

#[cfg(test)]
mod test {

    use super::*;

    use std::io::{
        Cursor
    };

    use std::collections::HashMap;

    fn dump_trie<F: Read + Write + Seek>(f: &mut F) -> () {
        fn space(cnt: usize) -> String {
            let mut ret = vec![];
            for _ in 0..cnt {
                ret.push(" ".to_string());
            }
            ret.join("")
        }

        fseek(f, 0).unwrap();

        let mut frontier : Vec<(TrieNodeType, usize)> = vec![];
        let (root, _) = Trie::read_root(f).unwrap();
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
                let (child_node, _) = Trie::read_node(f, ptr).unwrap();
                frontier.push((child_node, depth + path_len + 1));
            }
        }
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
    fn read_write_node4() {
        let mut node4 = TrieNode4::new(&vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19]);
        for i in 0..3 {
            assert!(node4.insert(&TriePtr::new(TrieNodeID::Node16, (i+1) as u8, (i+2) as u64)));
        }
        let mut buf = vec![0u8; 4096];
        let mut cursor = Cursor::new(&mut buf);
        let hash = DoubleSha256::from_data(&[0u8; 32]);
        let wres = Trie::write_nodetype(&mut cursor, &TrieNodeType::Node4(node4.clone()), hash.clone());
        assert!(wres.is_ok());
        assert!(wres.unwrap() > 0);

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
        let mut buf = vec![0u8; 4096];
        let mut cursor = Cursor::new(&mut buf);
        let hash = DoubleSha256::from_data(&[0u8; 32]);
        let wres = Trie::write_nodetype(&mut cursor, &TrieNodeType::Node16(node16.clone()), hash.clone());
        assert!(wres.is_ok());
        assert!(wres.unwrap() > 0);

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
        let mut buf = vec![0u8; 4096];
        let mut cursor = Cursor::new(&mut buf);
        let hash = DoubleSha256::from_data(&[0u8; 32]);
        let wres = Trie::write_nodetype(&mut cursor, &TrieNodeType::Node48(node48.clone()), hash.clone());
        assert!(wres.is_ok());
        assert!(wres.unwrap() > 0);

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
        let mut buf = vec![0u8; 4096];
        let mut cursor = Cursor::new(&mut buf);
        let hash = DoubleSha256::from_data(&[0u8; 32]);
        let wres = Trie::write_nodetype(&mut cursor, &TrieNodeType::Node256(node256.clone()), hash.clone());
        assert!(wres.is_ok());
        assert!(wres.unwrap() > 0);

        fseek(&mut cursor, 0).unwrap();
        let rres = Trie::read_node(&mut cursor, &TriePtr::new(TrieNodeID::Node256, 0, 0));
        
        assert!(rres.is_ok());
        assert_eq!(rres.unwrap(), (TrieNodeType::Node256(node256.clone()), hash));
    }

    #[test]
    fn read_write_node4_hashes() {
        let mut buf = vec![0u8; 4096];
        let mut cursor = Cursor::new(&mut buf);
        let mut node4 = TrieNode4::new(&vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18]);
        let hash = DoubleSha256::from_data(&[0u8; 32]);

        let mut child_hashes = vec![];
        for i in 0..3 {
            let mut child = TrieLeaf::new(&vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,i as u8], &vec![i as u8; 40]);
            let mut child_hash = Trie::<Cursor<Vec<u8>>>::get_node_hash(&child, &vec![]);

            child_hashes.push(child_hash.clone());

            let ptr = ftell(&mut cursor).unwrap();
            Trie::write_node(&mut cursor, &child, child_hash).unwrap();
            assert!(node4.insert(&TriePtr::new(TrieNodeID::Leaf, i as u8, ptr as u64)));
        }

        // no final child
        child_hashes.push(DoubleSha256::from_data(&[]));
        
        let node4_ptr = ftell(&mut cursor).unwrap();
        let node4_hash = Trie::<Cursor<Vec<u8>>>::get_node_hash(&node4, &child_hashes);
        Trie::write_node(&mut cursor, &node4, node4_hash).unwrap();

        fseek(&mut cursor, node4_ptr).unwrap();
        let read_child_hashes = Trie::get_children_hashes(&mut cursor, &TrieNodeType::Node4(node4)).unwrap();

        assert_eq!(read_child_hashes, child_hashes);
    }

    #[test]
    fn read_write_node16_hashes() {
        let mut buf = vec![0u8; 4096];
        let mut cursor = Cursor::new(&mut buf);
        let mut node16 = TrieNode16::new(&vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18]);
        let hash = DoubleSha256::from_data(&[0u8; 32]);

        let mut child_hashes = vec![];
        for i in 0..15 {
            let mut child = TrieLeaf::new(&vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,i as u8], &vec![i as u8; 40]);
            let mut child_hash = Trie::<Cursor<Vec<u8>>>::get_node_hash(&child, &vec![]);

            child_hashes.push(child_hash.clone());

            let ptr = ftell(&mut cursor).unwrap();
            Trie::write_node(&mut cursor, &child, child_hash).unwrap();
            assert!(node16.insert(&TriePtr::new(TrieNodeID::Leaf, i as u8, ptr as u64)));
        }

        // no final child
        child_hashes.push(DoubleSha256::from_data(&[]));
        
        let node16_ptr = ftell(&mut cursor).unwrap();
        let node16_hash = Trie::<Cursor<Vec<u8>>>::get_node_hash(&node16, &child_hashes);
        Trie::write_node(&mut cursor, &node16, node16_hash).unwrap();

        fseek(&mut cursor, node16_ptr).unwrap();
        let read_child_hashes = Trie::get_children_hashes(&mut cursor, &TrieNodeType::Node16(node16)).unwrap();

        assert_eq!(read_child_hashes, child_hashes);
    }

    #[test]
    fn read_write_node48_hashes() {
        let mut buf = vec![0u8; 4096];
        let mut cursor = Cursor::new(&mut buf);
        let mut node48 = TrieNode48::new(&vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18]);
        let hash = DoubleSha256::from_data(&[0u8; 32]);

        let mut child_hashes = vec![];
        for i in 0..47 {
            let mut child = TrieLeaf::new(&vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,i as u8], &vec![i as u8; 40]);
            let mut child_hash = Trie::<Cursor<Vec<u8>>>::get_node_hash(&child, &vec![]);

            child_hashes.push(child_hash.clone());

            let ptr = ftell(&mut cursor).unwrap();
            Trie::write_node(&mut cursor, &child, child_hash).unwrap();
            assert!(node48.insert(&TriePtr::new(TrieNodeID::Leaf, i as u8, ptr as u64)));
        }

        // no final child
        child_hashes.push(DoubleSha256::from_data(&[]));
        
        let node48_ptr = ftell(&mut cursor).unwrap();
        let node48_hash = Trie::<Cursor<Vec<u8>>>::get_node_hash(&node48, &child_hashes);
        Trie::write_node(&mut cursor, &node48, node48_hash).unwrap();

        fseek(&mut cursor, node48_ptr).unwrap();
        let read_child_hashes = Trie::get_children_hashes(&mut cursor, &TrieNodeType::Node48(node48)).unwrap();

        assert_eq!(read_child_hashes, child_hashes);
    }

    #[test]
    fn read_write_node256_hashes() {
        let mut buf = vec![0u8; 8192];
        let mut cursor = Cursor::new(&mut buf);
        let mut node256 = TrieNode256::new(&vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18]);
        let hash = DoubleSha256::from_data(&[0u8; 32]);

        let mut child_hashes = vec![];
        for i in 0..255 {
            let mut child = TrieLeaf::new(&vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,i as u8], &vec![i as u8; 40]);
            let mut child_hash = Trie::<Cursor<Vec<u8>>>::get_node_hash(&child, &vec![]);

            child_hashes.push(child_hash.clone());

            let ptr = ftell(&mut cursor).unwrap();
            Trie::write_node(&mut cursor, &child, child_hash).unwrap();
            assert!(node256.insert(&TriePtr::new(TrieNodeID::Leaf, i as u8, ptr as u64)));
        }

        // no final child
        child_hashes.push(DoubleSha256::from_data(&[]));
        
        let node256_ptr = ftell(&mut cursor).unwrap();
        let node256_hash = Trie::<Cursor<Vec<u8>>>::get_node_hash(&node256, &child_hashes);
        Trie::write_node(&mut cursor, &node256, node256_hash).unwrap();

        fseek(&mut cursor, node256_ptr).unwrap();
        let read_child_hashes = Trie::get_children_hashes(&mut cursor, &TrieNodeType::Node256(node256)).unwrap();

        assert_eq!(read_child_hashes, child_hashes);
    }

    fn make_node4_path<F: Read + Write + Seek>(f: &mut F, path_segments: &Vec<(Vec<u8>, u8)>, leaf_data: Vec<u8>) -> (Vec<TrieNodeType>, Vec<TriePtr>, Vec<DoubleSha256>) {
        // make a fully-fleshed-out path of node4's to a leaf 
        fseek(f, 0).unwrap();
        let root = TrieNode256::new(&path_segments[0].0);
        let root_hash = DoubleSha256::from_data(&[0u8; 32]);        // don't care about this in this test
        Trie::write_node(f, &root, root_hash.clone()).unwrap();

        let mut parent = TrieNodeType::Node256(root);
        let mut parent_ptr = 0;

        let mut nodes = vec![];
        let mut node_ptrs = vec![];
        let mut hashes = vec![];
        let mut seg_id = 0;

        for i in 0..path_segments.len() - 1 {
            let path_segment = &path_segments[i+1].0;
            let chr = path_segments[i].1;

            let node4 = TrieNode4::new(path_segment);
            let node4_ptr = ftell(f).unwrap();

            Trie::write_node(f, &node4, DoubleSha256::from_data(&[(seg_id+1) as u8; 32])).unwrap();
            let sav = ftell(f).unwrap();

            // update parent 
            fseek(f, parent_ptr).unwrap();

            match parent {
                TrieNodeType::Node256(ref mut data) => assert!(data.insert(&TriePtr::new(TrieNodeID::Node4, chr, node4_ptr as u64))),
                TrieNodeType::Node48(ref mut data) => assert!(data.insert(&TriePtr::new(TrieNodeID::Node4, chr, node4_ptr as u64))),
                TrieNodeType::Node16(ref mut data) => assert!(data.insert(&TriePtr::new(TrieNodeID::Node4, chr, node4_ptr as u64))),
                TrieNodeType::Node4(ref mut data) => assert!(data.insert(&TriePtr::new(TrieNodeID::Node4, chr, node4_ptr as u64))),
                TrieNodeType::Leaf(ref mut data) => panic!("can't insert into leaf")
            };

            Trie::write_nodetype(f, &parent, DoubleSha256::from_data(&[seg_id as u8; 32])).unwrap();
            
            fseek(f, sav).unwrap();
            
            nodes.push(parent.clone());
            node_ptrs.push(TriePtr::new(TrieNodeID::Node4, chr, node4_ptr as u64));
            hashes.push(DoubleSha256::from_data(&[(seg_id+1) as u8; 32]));

            parent = TrieNodeType::Node4(node4);
            parent_ptr = node4_ptr;

            seg_id += 1;
        }

        // add a leaf at the end 
        let child = TrieLeaf::new(&path_segments[path_segments.len()-1].0, &leaf_data);
        let child_chr = path_segments[path_segments.len()-1].1;
        let child_ptr = ftell(f).unwrap();
        Trie::write_node(f, &child, DoubleSha256::from_data(&[(seg_id+1) as u8; 32])).unwrap();

        // update parent
        let sav = ftell(f).unwrap();
        fseek(f, parent_ptr).unwrap();

        match parent {
            TrieNodeType::Node256(ref mut data) => assert!(data.insert(&TriePtr::new(TrieNodeID::Leaf, child_chr, child_ptr))),
            TrieNodeType::Node48(ref mut data) => assert!(data.insert(&TriePtr::new(TrieNodeID::Leaf, child_chr, child_ptr))),
            TrieNodeType::Node16(ref mut data) => assert!(data.insert(&TriePtr::new(TrieNodeID::Leaf, child_chr, child_ptr))),
            TrieNodeType::Node4(ref mut data) => assert!(data.insert(&TriePtr::new(TrieNodeID::Leaf, child_chr, child_ptr))),
            TrieNodeType::Leaf(ref mut data) => panic!("can't insert into leaf")
        };

        Trie::write_nodetype(f, &parent, DoubleSha256::from_data(&[(seg_id) as u8; 32])).unwrap();

        fseek(f, sav).unwrap();

        nodes.push(parent.clone());
        node_ptrs.push(TriePtr::new(TrieNodeID::Leaf, child_chr, child_ptr as u64));
        hashes.push(DoubleSha256::from_data(&[(seg_id+1) as u8; 32]));

        fseek(f, 0).unwrap();
        (nodes, node_ptrs, hashes)
    }

    #[test]
    fn trie_cursor_walk_full() {
        let mut buf = vec![0u8; 8192];
        let mut f = Cursor::new(&mut buf);

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
        let mut buf = vec![0u8; 8192];
        let mut f = Cursor::new(&mut buf);

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
        let mut buf = vec![0u8; 8192];
        let mut f = Cursor::new(&mut buf);

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
        let mut buf = vec![0u8; 8192];
        let mut f = Cursor::new(&mut buf);

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
        let mut buf = vec![0u8; 8192];
        let mut f = Cursor::new(&mut buf);

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
        let mut buf = vec![0u8; 8192];
        let mut f = Cursor::new(&mut buf);

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
        let mut buf = vec![0u8; 8192];
        let mut f = Cursor::new(&mut buf);

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
        let mut buf = vec![0u8; 8192];
        let mut f = Cursor::new(&mut buf);

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
        let mut buf = vec![0u8; 8192];
        let mut f = Cursor::new(&mut buf);

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
        let mut buf = vec![0u8; 8192];
        let mut f = Cursor::new(&mut buf);

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
                        let leaf_opt_res = Trie::get(&mut f, &TriePath::from_bytes(&path[..]).unwrap());
                        assert!(leaf_opt_res.is_ok());
                        
                        let leaf_opt = leaf_opt_res.unwrap();
                        assert!(leaf_opt.is_some());

                        let leaf = leaf_opt.unwrap();
                        assert_eq!(leaf, TrieLeaf::new(&path[i+1..].to_vec(), &[i as u8; 40].to_vec()));
                        break;
                    }
                }
            }
        }

        // look up each leaf we inserted
        for i in 0..20 {
            let mut path = vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19];
            path[i] = 20;

            let leaf_opt_res = Trie::get(&mut f, &TriePath::from_bytes(&path[..]).unwrap());
            assert!(leaf_opt_res.is_ok());
            
            let leaf_opt = leaf_opt_res.unwrap();
            assert!(leaf_opt.is_some());

            let leaf = leaf_opt.unwrap();
            assert_eq!(leaf, TrieLeaf::new(&path[i+1..].to_vec(), &[i as u8; 40].to_vec()));
        }

        // each ptr must be a node with two children
        for i in 0..20 {
            let ptr = &ptrs[i];
            let (node, hash) = Trie::read_node(&mut f, ptr).unwrap();
            match node {
                TrieNodeType::Node4(ref data) => {
                    assert_eq!(Trie::<Cursor<Vec<u8>>>::count_children(&data.ptrs), 2)
                },
                TrieNodeType::Node256(ref data) => {
                    assert_eq!(Trie::<Cursor<Vec<u8>>>::count_children(&data.ptrs), 2)
                },
                _ => assert!(false)
            };
        }
        
        dump_trie(&mut f);
    }

    #[test]
    fn trie_cursor_promote_leaf_to_node4() {
        let mut buf = vec![];
        let mut f = Cursor::new(&mut buf);

        Trie::format(&mut f).unwrap();
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

        assert_eq!(Trie::get(&mut f, &TriePath::from_bytes(&[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19]).unwrap()).unwrap().unwrap(), 
                   TrieLeaf::new(&vec![1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19], &[128; 40].to_vec()));

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
                        let leaf_opt_res = Trie::get(&mut f, &TriePath::from_bytes(&path[..]).unwrap());
                        assert!(leaf_opt_res.is_ok());
                        
                        let leaf_opt = leaf_opt_res.unwrap();
                        assert!(leaf_opt.is_some());

                        let leaf = leaf_opt.unwrap();
                        assert_eq!(leaf, TrieLeaf::new(&path[i+1..].to_vec(), &[(i + 128) as u8; 40].to_vec()));
                        break;
                    }
                }
            }
        }

        // look up each leaf we inserted
        for i in 1..20 {
            let mut path = vec![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19];
            path[i] = 20;

            let leaf_opt_res = Trie::get(&mut f, &TriePath::from_bytes(&path[..]).unwrap());
            assert!(leaf_opt_res.is_ok());
            
            let leaf_opt = leaf_opt_res.unwrap();
            assert!(leaf_opt.is_some());

            let leaf = leaf_opt.unwrap();
            assert_eq!(leaf, TrieLeaf::new(&path[i+1..].to_vec(), &[(i + 128) as u8; 40].to_vec()));
        }

        // each ptr must be a node with two children
        for i in 0..19 {
            let ptr = &ptrs[i];
            let (node, hash) = Trie::read_node(&mut f, ptr).unwrap();
            match node {
                TrieNodeType::Node4(ref data) => {
                    assert_eq!(Trie::<Cursor<Vec<u8>>>::count_children(&data.ptrs), 2)
                },
                TrieNodeType::Node256(ref data) => {
                    assert_eq!(Trie::<Cursor<Vec<u8>>>::count_children(&data.ptrs), 2)
                },
                _ => assert!(false)
            };
        }

        dump_trie(&mut f);
    }

    #[test]
    fn trie_cursor_promote_node4_to_node16() {
        let mut buf = vec![];
        let mut f = Cursor::new(&mut buf);

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
                assert_eq!(Trie::get(&mut f, &TriePath::from_bytes(&path[..]).unwrap()).unwrap().unwrap(),
                           TrieLeaf::new(&path[k+1..].to_vec(), &[128 + j as u8; 40].to_vec()));
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
            assert_eq!(Trie::get(&mut f, &TriePath::from_bytes(&path[..]).unwrap()).unwrap().unwrap(),
                       TrieLeaf::new(&path[k+1..].to_vec(), &[192 + k as u8; 40].to_vec()));
        }

        // each ptr we got should point to a node16 with 5 children
        for ptr in ptrs.iter() {
            let (node, hash) = Trie::read_node(&mut f, ptr).unwrap();
            match node {
                TrieNodeType::Node16(ref data) => {
                    assert_eq!(Trie::<Cursor<Vec<u8>>>::count_children(&data.ptrs), 5);
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
        let mut buf = vec![];
        let mut f = Cursor::new(&mut buf);

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
                assert_eq!(Trie::get(&mut f, &TriePath::from_bytes(&path[..]).unwrap()).unwrap().unwrap(),
                           TrieLeaf::new(&path[k+1..].to_vec(), &[128 + j as u8; 40].to_vec()));
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
            assert_eq!(Trie::get(&mut f, &TriePath::from_bytes(&path[..]).unwrap()).unwrap().unwrap(),
                       TrieLeaf::new(&path[k+1..].to_vec(), &[192 + k as u8; 40].to_vec()));
        }

        // each ptr we got should point to a node16 with 5 children
        for ptr in ptrs.iter() {
            let (node, hash) = Trie::read_node(&mut f, ptr).unwrap();
            match node {
                TrieNodeType::Node16(ref data) => {
                    assert_eq!(Trie::<Cursor<Vec<u8>>>::count_children(&data.ptrs), 5);
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
                assert_eq!(Trie::get(&mut f, &TriePath::from_bytes(&path[..]).unwrap()).unwrap().unwrap(),
                           TrieLeaf::new(&path[k+1..].to_vec(), &[128 + j as u8; 40].to_vec()));
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
            assert_eq!(Trie::get(&mut f, &TriePath::from_bytes(&path[..]).unwrap()).unwrap().unwrap(),
                       TrieLeaf::new(&path[k+1..].to_vec(), &[192 + k as u8; 40].to_vec()));
        }

        // each ptr we got should point to a node48 with 17 children
        for ptr in ptrs.iter() {
            let (node, hash) = Trie::read_node(&mut f, ptr).unwrap();
            match node {
                TrieNodeType::Node48(ref data) => {
                    assert_eq!(Trie::<Cursor<Vec<u8>>>::count_children(&data.ptrs), 17);
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
        let mut buf = vec![];
        let mut f = Cursor::new(&mut buf);

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
                assert_eq!(Trie::get(&mut f, &TriePath::from_bytes(&path[..]).unwrap()).unwrap().unwrap(),
                           TrieLeaf::new(&path[k+1..].to_vec(), &[128 + j as u8; 40].to_vec()));
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
            assert_eq!(Trie::get(&mut f, &TriePath::from_bytes(&path[..]).unwrap()).unwrap().unwrap(),
                       TrieLeaf::new(&path[k+1..].to_vec(), &[192 + k as u8; 40].to_vec()));
        }

        // each ptr we got should point to a node16 with 5 children
        for ptr in ptrs.iter() {
            let (node, hash) = Trie::read_node(&mut f, ptr).unwrap();
            match node {
                TrieNodeType::Node16(ref data) => {
                    assert_eq!(Trie::<Cursor<Vec<u8>>>::count_children(&data.ptrs), 5);
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
                assert_eq!(Trie::get(&mut f, &TriePath::from_bytes(&path[..]).unwrap()).unwrap().unwrap(),
                           TrieLeaf::new(&path[k+1..].to_vec(), &[128 + j as u8; 40].to_vec()));
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
            assert_eq!(Trie::get(&mut f, &TriePath::from_bytes(&path[..]).unwrap()).unwrap().unwrap(),
                       TrieLeaf::new(&path[k+1..].to_vec(), &[192 + k as u8; 40].to_vec()));
        }

        // each ptr we got should point to a node48 with 17 children
        for ptr in ptrs.iter() {
            let (node, hash) = Trie::read_node(&mut f, ptr).unwrap();
            match node {
                TrieNodeType::Node48(ref data) => {
                    assert_eq!(Trie::<Cursor<Vec<u8>>>::count_children(&data.ptrs), 17);
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
                assert_eq!(Trie::get(&mut f, &TriePath::from_bytes(&path[..]).unwrap()).unwrap().unwrap(),
                           TrieLeaf::new(&path[k+1..].to_vec(), &[128 + j as u8; 40].to_vec()));
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
            assert_eq!(Trie::get(&mut f, &TriePath::from_bytes(&path[..]).unwrap()).unwrap().unwrap(),
                       TrieLeaf::new(&path[k+1..].to_vec(), &[192 + k as u8; 40].to_vec()));
        }

        // each ptr we got should point to a node256 with 49 children
        for ptr in ptrs.iter() {
            let (node, hash) = Trie::read_node(&mut f, ptr).unwrap();
            match node {
                TrieNodeType::Node256(ref data) => {
                    assert_eq!(Trie::<Cursor<Vec<u8>>>::count_children(&data.ptrs), 49);
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
        let mut buf = vec![0u8; 8192];
        let mut f = Cursor::new(&mut buf);

        let path_segments = vec![
            (vec![0,1,2,3], 4),
            (vec![5,6,7,8], 9),
            (vec![10,11,12,13], 14),
            (vec![15,16,17,18], 19)
        ];

        let (nodes, node_ptrs, hashes) = make_node4_path(&mut f, &path_segments, [19u8; 40].to_vec());
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
            assert_eq!(Trie::get(&mut f, &TriePath::from_bytes(&path[..]).unwrap()).unwrap().unwrap(),
                       TrieLeaf::new(&path[4*k+3..].to_vec(), &[192 + k as u8; 40].to_vec()));
        }

        dump_trie(&mut f);
    }
    
    #[test]
    fn trie_cursor_splice_leaf_2() {
        let mut buf = vec![];
        let mut f = Cursor::new(&mut buf);

        let path_segments = vec![
            (vec![0,1], 2),
            (vec![3,4], 5),
            (vec![6,7], 8),
            (vec![9,10], 11),
            (vec![12,13], 14),
            (vec![15,16], 17),
            (vec![18], 19)
        ];

        let (nodes, node_ptrs, hashes) = make_node4_path(&mut f, &path_segments, [19u8; 40].to_vec());
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
            assert_eq!(Trie::get(&mut f, &TriePath::from_bytes(&path[..]).unwrap()).unwrap().unwrap(),
                       TrieLeaf::new(&path[3*k+2..].to_vec(), &[192 + k as u8; 40].to_vec()));
        }

        dump_trie(&mut f);
    }

    #[test]
    fn insert_1024_seq_low() {
        let mut buf = vec![];
        let mut f = Cursor::new(&mut buf);
        Trie::format(&mut f).unwrap();

        for i in 0..1024 {
            let i0 = i / 256;
            let i1 = i % 256;
            let path = [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,i0 as u8, i1 as u8];
            let triepath = TriePath::from_bytes(&path[..]).unwrap();
            let value = TrieLeaf::new(&vec![], &[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,i0 as u8, i1 as u8].to_vec());
            Trie::insert(&mut f, &triepath, &value).unwrap();
        }

        for i in 0..1024 {
            let i0 = i / 256;
            let i1 = i % 256;
            let path = [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,i0 as u8, i1 as u8];
            let triepath = TriePath::from_bytes(&path[..]).unwrap();
            let value = Trie::get(&mut f, &triepath).unwrap().unwrap();
            assert_eq!(value.reserved.to_vec(), [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,i0 as u8, i1 as u8].to_vec());
        }
        
        dump_trie(&mut f);
    }
    
    #[test]
    fn insert_1024_seq_high() {
        let mut buf = vec![];
        let mut f = Cursor::new(&mut buf);
        Trie::format(&mut f).unwrap();

        for i in 0..1024 {
            let i0 = i / 256;
            let i1 = i % 256;
            let path = [i0 as u8, i1 as u8, 2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19];
            let triepath = TriePath::from_bytes(&path[..]).unwrap();
            let value = TrieLeaf::new(&vec![], &[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,i0 as u8, i1 as u8].to_vec());
            Trie::insert(&mut f, &triepath, &value).unwrap();
        }

        for i in 0..1024 {
            let i0 = i / 256;
            let i1 = i % 256;
            let path = [i0 as u8, i1 as u8, 2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19];
            let triepath = TriePath::from_bytes(&path[..]).unwrap();
            let value = Trie::get(&mut f, &triepath).unwrap().unwrap();
            assert_eq!(value.reserved.to_vec(), [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,i0 as u8, i1 as u8].to_vec());
        }
        
        dump_trie(&mut f);
    }
    
    #[test]
    fn insert_1024_seq_mid() {
        let mut buf = vec![];
        let mut f = Cursor::new(&mut buf);
        Trie::format(&mut f).unwrap();

        for i in 0..1024 {
            let i0 = i / 256;
            let i1 = (i % 256) / 32;
            let i2 = (i % 256) % 32;
            let i3 = (i % 256) % 16;
            let path = [0,1,i0 as u8,i1 as u8,i2 as u8,i3 as u8,6,7,8,9,10,11,12,13,14,15,16,17,18,19];
            let triepath = TriePath::from_bytes(&path[..]).unwrap();
            let value = TrieLeaf::new(&vec![], &[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,i0 as u8, i1 as u8].to_vec());
            Trie::insert(&mut f, &triepath, &value).unwrap();
        }

        for i in 0..1024 {
            let i0 = i / 256;
            let i1 = (i % 256) / 32;
            let i2 = (i % 256) % 32;
            let i3 = (i % 256) % 16;
            let path = [0,1,i0 as u8,i1 as u8,i2 as u8,i3 as u8,6,7,8,9,10,11,12,13,14,15,16,17,18,19];
            let triepath = TriePath::from_bytes(&path[..]).unwrap();
            let value = Trie::get(&mut f, &triepath).unwrap().unwrap();
            assert_eq!(value.reserved.to_vec(), [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,i0 as u8, i1 as u8].to_vec());
        }
        
        dump_trie(&mut f);
    }
    
    #[test]
    fn insert_65536_random_deterministic() {
        // deterministic random insert of 65536 keys
        let mut buf = vec![];
        let mut f = Cursor::new(&mut buf);
        Trie::format(&mut f).unwrap();

        let mut seed = DoubleSha256::from_data(&[]).as_bytes().to_vec();

        for i in 0..65536 {
            let i0 = i / 256;
            let i1 = i % 256;
            let path = DoubleSha256::from_data(&seed[..]).as_bytes()[0..20].to_vec();
            seed = path.clone();

            let triepath = TriePath::from_bytes(&path[..]).unwrap();
            let value = TrieLeaf::new(&vec![], &[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,i0 as u8, i1 as u8].to_vec());
            Trie::insert(&mut f, &triepath, &value).unwrap();
        }

        seed = DoubleSha256::from_data(&[]).as_bytes().to_vec();

        for i in 0..65536 {
            let i0 = i / 256;
            let i1 = i % 256;
            let path = DoubleSha256::from_data(&seed[..]).as_bytes()[0..20].to_vec();
            seed = path.clone();
            
            let triepath = TriePath::from_bytes(&path[..]).unwrap();
            let value = Trie::get(&mut f, &triepath).unwrap().unwrap();
            assert_eq!(value.reserved.to_vec(), [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,i0 as u8, i1 as u8].to_vec());
        }
        
        dump_trie(&mut f);
    }
    
    #[test]
    fn insert_1024_random_deterministic_merkle_proof() {
        // deterministic random insert of 1024 keys
        let mut buf = vec![];
        let mut f = Cursor::new(&mut buf);
        Trie::format(&mut f).unwrap();

        let mut seed = DoubleSha256::from_data(&[]).as_bytes().to_vec();
        let mut merkle_proofs = HashMap<String, String>::new();
        
        for i in 0..1024 {
            let i0 = i / 256;
            let i1 = i % 256;
            let path = DoubleSha256::from_data(&seed[..]).as_bytes()[0..20].to_vec();
            seed = path.clone();

            let triepath = TriePath::from_bytes(&path[..]).unwrap();
            let value = TrieLeaf::new(&vec![], &[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,i0 as u8, i1 as u8].to_vec());
            Trie::insert(&mut f, &triepath, &value).unwrap();

            
        }

        seed = DoubleSha256::from_data(&[]).as_bytes().to_vec();

        for i in 0..1024 {
            let i0 = i / 256;
            let i1 = i % 256;
            let path = DoubleSha256::from_data(&seed[..]).as_bytes()[0..20].to_vec();
            seed = path.clone();
            
            let triepath = TriePath::from_bytes(&path[..]).unwrap();
            let value = Trie::get(&mut f, &triepath).unwrap().unwrap();
            assert_eq!(value.reserved.to_vec(), [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,i0 as u8, i1 as u8].to_vec());
        }
        
        dump_trie(&mut f);
    }

    // TODO:
    // * merkle proof generation & verification
}
