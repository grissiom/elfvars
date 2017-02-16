use std::env;
use std::fs;
use std::io;
use std::io::prelude::*;
//use std::ffi;
use std::borrow::Borrow;
use std::borrow::Cow;
use std::error;
use std::result;
use std::fmt::{self, Debug};
use std::collections::HashMap;

#[macro_use]
extern crate serde_derive;

extern crate serde_json;

extern crate getopts;
#[macro_use]
extern crate log;
extern crate env_logger;

extern crate gimli;
extern crate xmas_elf;

//mod dwarf;

#[derive(Debug)]
pub struct Error(pub Cow<'static,  str>);

impl error::Error for Error {
    fn description(&self) -> &str {
        self.0.borrow()
    }
}

impl fmt::Display for Error {
    fn fmt(&self,  f: &mut fmt::Formatter) -> fmt::Result {
        write!(f,  "{}",  self.0)
    }
}

impl From<&'static str> for Error {
    fn from(s: &'static str) -> Error {
        Error(Cow::Borrowed(s))
    }
}

impl From<String> for Error {
    fn from(s: String) -> Error {
        Error(Cow::Owned(s))
    }
}

impl From<std::io::Error> for Error {
    fn from(e: std::io::Error) -> Error {
        Error(Cow::Owned(format!("IO error: {}",  e)))
    }
}

impl From<std::str::Utf8Error> for Error {
    fn from(e: std::str::Utf8Error) -> Error {
        Error(Cow::Owned(format!("UTF-8 error: {}",  e)))
    }
}

impl From<gimli::Error> for Error {
    fn from(e: gimli::Error) -> Error {
        Error(Cow::Owned(format!("DWARF error: {}",  e)))
    }
}

pub type Result<T> = result::Result<T, Error>;

fn main() {
    env_logger::init().unwrap();

    let opts = getopts::Options::new();
    let matches = match opts.parse(env::args().skip(1)) {
        Ok(m) => m,
        Err(e) => {
            error!("{}", e);
            print_usage(&opts);
        }
    };

    if matches.free.len() != 1 {
        error!("Invalid filename arguments (expected 1 filename, found {})",
        matches.free.len());
        print_usage(&opts);
    }
	let path = &matches.free[0];

    let mut file = match fs::File::open(path) {
        Ok(file) => file,
        Err(e) => {
            error!("open {} failed: {}", path, e);
            return;
        }
    };
    let mut buffer = Vec::new();

    if let Err(e) = file.read_to_end(&mut buffer) {
        error!("{}: {}", path, e);
        return;
    }

    let mut result = HashMap::new();

    match parse_data(buffer.as_slice(), &mut result) {
        Ok(_) => {
            println!("{}", serde_json::to_string_pretty(&result).unwrap())
        }
        Err(e) => {
            error!("{}: {}", path, e);
            return;
        }
    }
}

pub fn parse_data<'input>(buffer: &'input [u8], out: &mut HashMap<String, u64>) -> Result<()> {
    let elf = xmas_elf::ElfFile::new(buffer);

    match elf.header.pt1.data {
        xmas_elf::header::Data::LittleEndian => parse::<gimli::LittleEndian>(&elf, out),
        xmas_elf::header::Data::BigEndian => parse::<gimli::BigEndian>(&elf, out),
        _ => {
            return Err("Unknown endianity".into());
        }
    }
}

fn print_usage(opts: &getopts::Options) -> ! {
    let brief = format!("Usage: {} <options> <file>", env::args().next().unwrap());
    write!(&mut io::stderr(), "{}", opts.usage(&brief)).ok();
    std::process::exit(1);
}

#[derive(Serialize, Debug, Default)]
pub struct Variable {
    name: String,
    addr: u64,
}

pub fn parse<'input, Endian>(elf: &xmas_elf::ElfFile<'input>,
                             out: &mut HashMap<String, u64>) -> Result<()>
    where Endian: gimli::Endianity
{
    let debug_abbrev = elf.find_section_by_name(".debug_abbrev").map(|s| s.raw_data(elf));
    let debug_abbrev = gimli::DebugAbbrev::<Endian>::new(debug_abbrev.unwrap_or(&[]));
    let debug_info = elf.find_section_by_name(".debug_info").map(|s| s.raw_data(elf));
    let debug_info = gimli::DebugInfo::<Endian>::new(debug_info.unwrap_or(&[]));
    let debug_str = elf.find_section_by_name(".debug_str").map(|s| s.raw_data(elf));
    let debug_str = gimli::DebugStr::<Endian>::new(debug_str.unwrap_or(&[]));

    let mut unit_headers = debug_info.units();
    while let Some(unit_header) = unit_headers.next()? {
        //println!("parse unit@ {:?}", unit_header.offset());
        parse_unit(&unit_header, debug_abbrev, debug_str, out)?;
    }
    Ok(())
}

fn parse_unit<'input, Endian>(
    unit_header: &gimli::CompilationUnitHeader<'input, Endian>,
    dbg_abbrev: gimli::DebugAbbrev<'input, Endian>,
    dbg_string: gimli::DebugStr<'input, Endian>,
    out: &mut HashMap<String, u64>
) -> Result<()>
    where Endian: gimli::Endianity
{
    let abbrev = &unit_header.abbreviations(dbg_abbrev)?;

    let mut cursor = unit_header.entries(abbrev);
    // Move the cursor to the root.
    assert!(cursor.next_dfs().unwrap().is_some());

	// Keep looping while the cursor is moving deeper into the DIE tree.
	while let Some((delta_depth, current)) = cursor.next_dfs()? {
		// 0 means we moved to a sibling, a negative number means we went back
		// up to a parent's sibling. In either case, bail out of the loop because
		//  we aren't going deeper into the tree anymore.
		if delta_depth <= 0 {
            debug!("break when {}, {:?}",
                   delta_depth, current.tag());
			//break;
		}

		match current.tag() {
			gimli::DW_TAG_compile_unit => {
                println!("break in CU");
                return Ok(());
            }
			gimli::DW_TAG_namespace => {
				//parse_namespace(unit, dwarf, dwarf_unit, namespace, child)?;
			}
			gimli::DW_TAG_subprogram => {
				//parse_subprogram(unit, dwarf, dwarf_unit, namespace, child)?;
			}
			gimli::DW_TAG_variable => {
				//vars.push(Variable{CIE: current});
                add_variable(current, dbg_string, out)?;
			}
			gimli::DW_TAG_base_type |
				gimli::DW_TAG_structure_type |
				gimli::DW_TAG_union_type |
				gimli::DW_TAG_enumeration_type |
				gimli::DW_TAG_array_type |
				gimli::DW_TAG_subroutine_type |
				gimli::DW_TAG_typedef |
				gimli::DW_TAG_const_type |
				gimli::DW_TAG_pointer_type |
				gimli::DW_TAG_restrict_type => {
					//let ty = parse_type(unit, dwarf, dwarf_unit, namespace, child)?;
					//unit.types.insert(offset.0, ty);
				}
			tag => {
				debug!("unknown namespace child tag: {}", tag);
			}
		}
	}

    Ok(())
}

fn add_variable<'input, 'abbrev, 'unit, Endian>(die: &gimli::DebuggingInformationEntry<'input,
                                                'abbrev, 'unit, Endian>,
                                dbg_string: gimli::DebugStr<'input, Endian>,
                                out: &mut HashMap<String, u64>
                               ) -> Result<()>
    where Endian: gimli::Endianity,
{
    assert!(die.tag() == gimli::DW_TAG_variable);


    let mut name = None;
    let mut addr = None;

    let mut attrs = die.attrs();
    while let Some(attr) = attrs.next()? {
        match attr.name() {
            gimli::DW_AT_name => {
                if let Some(s) = attr.string_value(&dbg_string) {
                    let ss = try!(s.to_str());
                    name = Some(ss.to_string());
                }
            }
            gimli::DW_AT_linkage_name => {
            }
            gimli::DW_AT_type => {
                if let gimli::AttributeValue::UnitRef(offset) = attr.value() {
                    //variable.ty = Some(offset);
                }
            }
            gimli::DW_AT_declaration => {
                if let gimli::AttributeValue::Flag(flag) = attr.value() {
                    if flag {
                        // We don't interest on varible declarations.
                        //return Ok(());
                    }
                }
            }
            gimli::DW_AT_location => {
                //println!("DW_AT_location: {:?}", attr);
                match attr.value() {
                    //gimli::AttributeValue::Addr(addr) => variable.location = Some(addr),
                    gimli::AttributeValue::Exprloc(gimli::EndianBuf(buf, _)) => {
                        if let Some((&first, elements)) = buf.split_first() {
                            if gimli::DwOp(first) == gimli::DW_OP_addr {
                                addr = match elements.len() {
                                    4 => {
                                        Some(Endian::read_u32(elements) as u64)
                                    }
                                    8 => {
                                        Some(Endian::read_u64(elements))
                                    }
                                    _ => {None}
                                }
                            } else {
                                // We only interest on variables that has fixed address.
                                return Ok(());
                            }
                        }
                    }
                    _ => {
                        // We only interest on variables that has fixed address.
                        return Ok(());
                    }
                }
            }
            gimli::DW_AT_artificial |
                gimli::DW_AT_external => {
                if let gimli::AttributeValue::Flag(flag) = attr.value() {
                    if flag {
                        // We only interest on concrete varibles.
                        return Ok(());
                    }
                }
            }
            gimli::DW_AT_abstract_origin |
                gimli::DW_AT_const_value |
                gimli::DW_AT_decl_file |
                gimli::DW_AT_decl_line => {}
            _ => {
                debug!("unknown variable attribute: {} {:?}",
                       attr.name(),
                       attr.value())
            }
        }
    }

    if let Some(n) = name{
        if let Some(a) = addr {
            out.insert(n, a);
        }
    }
    Ok(())
}
