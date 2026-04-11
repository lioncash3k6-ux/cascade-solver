//! DIMACS CNF parser. Streaming, no allocations beyond clause lits.

use crate::types::{Clause, Lit};
use std::fs::File;
use std::io::{BufRead, BufReader, Read};
use std::path::Path;

#[derive(Debug, Clone)]
pub struct Cnf {
    pub nvars: u32,
    pub clauses: Vec<Clause>,
}

#[derive(Debug)]
pub enum ParseError {
    Io(std::io::Error),
    BadHeader(String),
    BadLiteral(String),
    MissingHeader,
    MissingZero(usize),
}

impl From<std::io::Error> for ParseError {
    fn from(e: std::io::Error) -> ParseError {
        ParseError::Io(e)
    }
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ParseError::Io(e) => write!(f, "io: {}", e),
            ParseError::BadHeader(s) => write!(f, "bad header: {}", s),
            ParseError::BadLiteral(s) => write!(f, "bad literal: {}", s),
            ParseError::MissingHeader => write!(f, "missing 'p cnf' header"),
            ParseError::MissingZero(line) => {
                write!(f, "clause at line {} missing 0 terminator", line)
            }
        }
    }
}

impl std::error::Error for ParseError {}

pub fn parse_file<P: AsRef<Path>>(path: P) -> Result<Cnf, ParseError> {
    let f = File::open(path)?;
    parse_reader(BufReader::new(f))
}

pub fn parse_reader<R: Read>(reader: BufReader<R>) -> Result<Cnf, ParseError> {
    let mut nvars = 0u32;
    let mut nclauses_declared = 0usize;
    let mut clauses = Vec::new();
    let mut current = Vec::new();
    let mut header_seen = false;
    let mut line_num = 0usize;

    for line in reader.lines() {
        let line = line?;
        line_num += 1;
        let trimmed = line.trim_start();
        if trimmed.is_empty() || trimmed.starts_with('c') {
            continue;
        }
        if let Some(rest) = trimmed.strip_prefix("p cnf") {
            let parts: Vec<&str> = rest.split_whitespace().collect();
            if parts.len() < 2 {
                return Err(ParseError::BadHeader(line.clone()));
            }
            nvars = parts[0]
                .parse()
                .map_err(|_| ParseError::BadHeader(line.clone()))?;
            nclauses_declared = parts[1]
                .parse()
                .map_err(|_| ParseError::BadHeader(line.clone()))?;
            header_seen = true;
            continue;
        }
        if !header_seen {
            return Err(ParseError::MissingHeader);
        }
        for tok in trimmed.split_whitespace() {
            let n: i32 = tok
                .parse()
                .map_err(|_| ParseError::BadLiteral(tok.to_string()))?;
            if n == 0 {
                clauses.push(Clause::new(std::mem::take(&mut current)));
            } else {
                current.push(Lit::new(n));
            }
        }
    }

    if !header_seen {
        return Err(ParseError::MissingHeader);
    }
    if !current.is_empty() {
        return Err(ParseError::MissingZero(line_num));
    }
    let _ = nclauses_declared;  // we don't enforce; extra/missing clauses are ok

    Ok(Cnf { nvars, clauses })
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Cursor;

    #[test]
    fn parse_simple() {
        let cnf = b"p cnf 3 2\n1 -2 3 0\n-1 2 0\n";
        let r = parse_reader(BufReader::new(Cursor::new(&cnf[..]))).unwrap();
        assert_eq!(r.nvars, 3);
        assert_eq!(r.clauses.len(), 2);
        assert_eq!(r.clauses[0].lits().len(), 3);
        assert_eq!(r.clauses[1].lits().len(), 2);
    }

    #[test]
    fn parse_with_comments() {
        let cnf = b"c hello\nc world\np cnf 2 1\n1 2 0\n";
        let r = parse_reader(BufReader::new(Cursor::new(&cnf[..]))).unwrap();
        assert_eq!(r.nvars, 2);
        assert_eq!(r.clauses.len(), 1);
    }

    #[test]
    fn parse_empty_clause() {
        let cnf = b"p cnf 1 1\n0\n";
        let r = parse_reader(BufReader::new(Cursor::new(&cnf[..]))).unwrap();
        assert_eq!(r.clauses.len(), 1);
        assert!(r.clauses[0].is_empty());
    }
}
