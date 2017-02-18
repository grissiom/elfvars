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
use std::rc::Rc;

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
pub struct Error(pub Cow<'static, str>);

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

    let mut opts = getopts::Options::new();
    opts.optopt("o", "output", "Set output file name", "FILE");
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

    match parse_data(buffer.as_slice()) {
        Ok(result) => {
            let data = serde_json::to_string_pretty(&result).unwrap();

            if let Some(fname) = matches.opt_str("o") {
                let mut file = fs::File::create(fname).unwrap();
                file.write_all(data.as_bytes()).unwrap();
            } else {
                println!("{}", data);
            }
        }
        Err(e) => {
            error!("{}: {}", path, e);
            return;
        }
    }
}

pub fn parse_data<'input>(buffer: &'input [u8]) -> Result<HashMap<String, Variable>> {
    let elf = xmas_elf::ElfFile::new(buffer);

    match elf.header.pt1.data {
        xmas_elf::header::Data::LittleEndian => parse::<gimli::LittleEndian>(&elf),
        xmas_elf::header::Data::BigEndian => parse::<gimli::BigEndian>(&elf),
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

// Rust does not have anonymous struct and union types yet...
#[derive(Serialize, Debug, Default)]
struct VarChildren {
    name: String,
    addr: u64,
    size: usize,
}

#[derive(Serialize, Debug, Default)]
pub struct Variable {
    // The variable name is the key of the hashmap.
    cu_name: Rc<String>,
    addr: u64,
    size: usize,
    children: Vec<VarChildren>,
}

pub fn parse<'input, Endian>(elf: &xmas_elf::ElfFile<'input>,
                            ) -> Result<HashMap<String, Variable>>
    where Endian: gimli::Endianity + std::marker::Send
{
    let mut out = HashMap::new();

    let debug_abbrev = elf.find_section_by_name(".debug_abbrev").map(|s| s.raw_data(elf));
    let debug_abbrev = gimli::DebugAbbrev::<Endian>::new(debug_abbrev.unwrap_or(&[]));
    let debug_info = elf.find_section_by_name(".debug_info").map(|s| s.raw_data(elf));
    let debug_info = gimli::DebugInfo::<Endian>::new(debug_info.unwrap_or(&[]));
    let debug_str = elf.find_section_by_name(".debug_str").map(|s| s.raw_data(elf));
    let debug_str = gimli::DebugStr::<Endian>::new(debug_str.unwrap_or(&[]));

    let mut unit_headers = debug_info.units();

    while let Some(unit_header) = unit_headers.next()? {
        out.extend(parse_unit(&unit_header, &debug_abbrev, &debug_str)?);
    }

    Ok(out)
}

fn parse_unit<'input, Endian>(
    unit_header: &gimli::CompilationUnitHeader<'input, Endian>,
    dbg_abbrev: &gimli::DebugAbbrev<'input, Endian>,
    dbg_string: &gimli::DebugStr<'input, Endian>,
) -> Result<HashMap<String, Variable>>
    where Endian: gimli::Endianity
{
    let mut out = HashMap::new();
    let abbrev = &unit_header.abbreviations(*dbg_abbrev)?;

    let mut cursor = unit_header.entries(abbrev);

    let mut cu_name = None;

    if let Some((_, cudie)) = cursor.next_dfs()? {
        if cudie.tag() != gimli::DW_TAG_compile_unit {
            return Err(Error(Cow::from("wrong CU DIE")));
        }

        if let Some(at_name) = cudie.attr(gimli::DW_AT_name)? {
            if let Some(s) = at_name.string_value(dbg_string) {
                let ss = try!(s.to_str());
                cu_name = Some(Rc::new(ss.to_string()));
            }
        }
    } else {
        return Err(Error(Cow::from("wrong CU DIE")));
    }

    if cu_name.is_none() {
        return Err(Error(Cow::from("no CU name")));
    }

    let cu_name = cu_name.unwrap();

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
			gimli::DW_TAG_namespace => {
			}
			gimli::DW_TAG_subprogram => {
			}
			gimli::DW_TAG_variable => {
                add_variable(current, cu_name.clone(), dbg_string, &mut out)?;
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
				}
			tag => {
				debug!("unknown namespace child tag: {}", tag);
			}
		}
	}

    Ok(out)
}

fn add_variable<'input, 'abbrev,
   'unit, Endian>(die: &gimli::DebuggingInformationEntry<'input, 'abbrev, 'unit, Endian>,
                  cu_name: Rc<String>,
                  dbg_string: &gimli::DebugStr<'input, Endian>,
                  out: &mut HashMap<String, Variable>
                               ) -> Result<()>
    where Endian: gimli::Endianity,
{
    assert!(die.tag() == gimli::DW_TAG_variable);


    let mut name = None;
    let mut var = Variable{cu_name: cu_name, ..Default::default()};

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
                    gimli::AttributeValue::Exprloc(gimli::EndianBuf(buf, _)) => {
                        if let Some((&first, elements)) = buf.split_first() {
                            if gimli::DwOp(first) == gimli::DW_OP_addr {
                                var.addr = match elements.len() {
                                    4 => {
                                        Endian::read_u32(elements) as u64
                                    }
                                    8 => {
                                        Endian::read_u64(elements)
                                    }
                                    _ => 0
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

    if let Some(n) = name {
        if var.addr != 0 {
            out.insert(n, var);
        }
    }
    Ok(())
}
