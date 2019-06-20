#![allow(unused_imports)]
#![allow(unused_assignments)]
#![allow(unused_variables)]
#![allow(dead_code)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]

extern crate sha2;
extern crate rand;

#[macro_use] mod util;

use std::env;
use std::process;
use std::io::{Read,Write,Seek,Error,ErrorKind};

use util::*;

fn main() {
    let argv : Vec<String> = env::args().collect();
    if argv.len() < 2 {
        eprintln!("Usage: {} [command] [args...]", argv[0]);
        process::exit(1);
    }

    match argv[1].as_str() {
        "dump_trie" => {
            if argv.len() != 4 {
                eprintln!("Usage: {} dump_trie /path/to/marf block_header_hash", argv[0]);
                process::exit(1);
            }
            let mut storage = TrieFileStorage::new(&argv[2]).unwrap();
            let bhh = BlockHeaderHash::from_hex(&argv[3]).unwrap();
            storage.open(&bhh, false).unwrap();
            print_trie(&mut storage);
        },
        _ => {
            eprintln!("Usage: {} do-stuff ...", argv[0]);
            process::exit(1);
        }
    }

    process::exit(0);
}
