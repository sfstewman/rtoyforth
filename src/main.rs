enum Data {
    Int(i32),
    Flt(f32),
    Str(String),
    Ptr(usize),
}

struct ToyForth {
    data_stack: Vec<Data>,
    dict: Vec<Data>,
    names: std::collections::HashMap<String,usize>,
}

#[derive(Debug,PartialEq)]
enum LexErrorType {
    UnterminatedString,
    InvalidNumber,
    InvalidEscape,
    InvalidIdent,
    // InvalidChar,
}

#[derive(Debug, PartialEq)]
struct LexError {
    error: LexErrorType,
    ind0: usize,
    ind1: usize,
}

#[derive(Debug, PartialEq)]
struct LexError1<'a> {
    error: LexErrorType,
    source: &'a str,
}

#[derive(Debug, PartialEq)]
enum Token {
    Str(String),
    Integer(i32),
    Float(f32),
    Ident(String),
}

#[derive(Debug, PartialEq)]
struct LexToken<'a> {
    token: Token,
    source: &'a str,
}

impl<'a> LexToken<'a> {
    fn str(v: &str, src: &'a str) -> LexToken<'a> {
        return LexToken{
            token: Token::Str(v.to_string()),
            source: src,
        };
    }

    fn string(v: String, src: &'a str) -> LexToken<'a> {
        return LexToken{
            token: Token::Str(v),
            source: src,
        };
    }

    fn ident(v: &'a str) -> LexToken<'a> {
        return LexToken{
            token: Token::Ident(v.to_string()),
            source: v,
        };
    }

    fn int(v: i32, src: &'a str) -> LexToken<'a> {
        return LexToken{
            token: Token::Integer(v),
            source: src,
        };
    }

    fn flt(v: f32, src: &'a str) -> LexToken<'a> {
        return LexToken{
            token: Token::Float(v),
            source: src,
        };
    }

    fn parse_num(v: &'a str) -> std::result::Result<LexToken<'a>, LexError1> {
        /* FIXME: better handling of errors here, especially various kinds of
         * overflow
         */
        if let Ok(x) = v.parse::<i32>() {
            return Ok(LexToken{
                token: Token::Integer(x),
                source: v,
            });
        }
        else if let Ok(x) = v.parse::<f32>() {
            return Ok(LexToken{
                token: Token::Float(x),
                source: v,
            });
        }
        else {
            return Err(LexError1{
                error: LexErrorType::InvalidNumber,
                source: v,
            });
        }
    }
}

impl Data {
    fn from_token(tok: LexToken) -> Result<Data,String> {
        match tok.token {
            Token::Str(v) => { Ok(Data::Str(v)) },
            Token::Integer(v) => { Ok(Data::Int(v)) },
            Token::Float(v) => { Ok(Data::Flt(v)) },
            // FIXME: handle ident lookup
            _ => { Err("ident not yet implemented".to_string()) },
        }
    }
}

struct Lexer<'a> {
    buf: &'a str,
    pos: usize,
}

fn tokenize<'a>(v: &'a str) -> Lexer<'a> {
    return Lexer{ buf: v, pos: 0 };
}

trait Tokenizer<'a> {
    type Item;
    fn next_str(&self, v: &'a str) -> (Option<Self::Item>,usize);
    fn next_num(&self, v: &'a str) -> (Option<Self::Item>,usize);
    fn next_ident(&self, v: &'a str) -> (Option<Self::Item>,usize);
}

impl<'a> Tokenizer<'a> for Lexer<'a> {
    type Item = std::result::Result<LexToken<'a>, LexError1<'a>>;

    fn next_str(&self, v: &'a str) -> (Option<Self::Item>,usize) {
        let mut iter = v.char_indices().peekable();
        let mut is_esc = false;
        let mut s = String::new();

        while let Some((i,ch)) = iter.next() {
            if is_esc {
                let esc_ch = match ch {
                    'n'  => { Some('\n') },
                    'r'  => { Some('\r') },
                    't'  => { Some('\t') },
                    '\\' => { Some('\\') },
                    '"'  => { Some('"')  },
                    _    => { None },
                };

                if let Some(c) = esc_ch {
                    s.push(c);
                    is_esc = false;
                } else {
                    return (Some(Err(LexError1{
                        error: LexErrorType::InvalidEscape,
                        source: &v,
                    })), i);
                }
            } else {
                match ch {
                    '\\' => { is_esc = true; },
                    '"' => {
                        return (Some(Ok(LexToken::string(s, &v[..i]))), i+1);
                    },
                    _ => {
                        s.push(ch);
                    }
                }
            }
        }

        return (Some(Err(LexError1{
            error: LexErrorType::UnterminatedString,
            source: &v,
        })), v.len());
    }

    fn next_num(&self, v: &'a str) -> (Option<Self::Item>,usize) {
        // eprintln!("next_num({})", v);
        let mut it = v.char_indices().peekable();
        if let Some((_,ch)) = it.peek() {
            if *ch == '+' || *ch == '-' {
                it.next();
            }
        }

        let after = it.skip_while(|(_,ch)| !ch.is_whitespace()).next();

        match after {
            Some((i,ch)) if ch.is_whitespace() => {
                return (Some(LexToken::parse_num(&v[..i])), i);
            },
            Some((i,_)) => {
                return (Some(Err(LexError1{
                    error: LexErrorType::InvalidNumber,
                    source: &v[..i],
                })), i);
            },
            None => {
                return (Some(LexToken::parse_num(&v)), v.len());
            }
        }
    }

    fn next_ident(&self, v: &'a str) -> (Option<Self::Item>,usize) {
        let after = v.char_indices().skip_while(|(_,ch)| !ch.is_whitespace()).next();

        match after {
            Some((i,_)) => {
                if let Some(_) = &v[..i].find(|c| c == '"' || c == '\\') {
                    return (Some(Err(LexError1{
                        error: LexErrorType::InvalidIdent,
                        source: &v[..i],
                    })), i);
                }

                return (Some(Ok(LexToken::ident(&v[..i]))), i);
            },
            None => {
                return (Some(Ok(LexToken::ident(v))), v.len());
            }
        }
    }
}

impl<'a> Iterator for Lexer<'a> {
    type Item = std::result::Result<LexToken<'a>, LexError1<'a>>;

    fn next(&mut self) -> Option<Self::Item> {
        let mut iter = self.buf[self.pos..].char_indices().skip_while(|(_,ch)| ch.is_whitespace()).peekable();
        if let Some((i,ch)) = iter.next() {
            // eprintln!("i={}, ch={}, buf=\"{}\" ^ \"{}\"", i, ch, &self.buf[..self.pos], &self.buf[self.pos..]);
            let (res,ind) = match ch {
                ch if ch.is_digit(10) => {
                    let ind0 = self.pos+i;
                    self.next_num(&self.buf[ind0..])
                },

                '"' => {
                    if let Some((next_i,_)) = iter.peek() {
                        let ind0 = self.pos+next_i;
                        let (res,ind1) = self.next_str(&self.buf[ind0..]);
                        (res,1+ind1)
                    } else {
                        let ind0 = self.pos+i;
                        (Some(Err(LexError1::<'a>{ error: LexErrorType::UnterminatedString, source: &self.buf[ind0..] })), 0)
                    }
                },

                '-' | '+' => {
                    let ind0 = self.pos + i;
                    match iter.peek() {
                        Some((_,next_ch)) if next_ch.is_digit(10) => {
                            self.next_num(&self.buf[ind0..])
                        },
                        _ => {
                            self.next_ident(&self.buf[ind0..])
                        }
                    }
                },

                _ => {
                    let ind0 = self.pos+i;
                    self.next_ident(&self.buf[ind0..])
                }
            };

            // eprintln!("res = {:?}, i={}, ind={}, self.pos={}", res, i, ind, self.pos);
            if let Some(_) = res {
                self.pos += i + ind;
            }

            return res;
        }
        else {
            return None;
        }
    }
}

impl ToyForth {
    fn new() -> ToyForth {
        return ToyForth{
            data_stack: Vec::new(),
            dict: Vec::new(),
            names: std::collections::HashMap::new(),
        };
    }

    fn process_token(&mut self, tok: LexToken) -> Result<(), String> {
        println!("token: {} source: {}", tok.token, tok.source);
        if let Token::Ident(id) = tok.token {
            /*
            match self.lookup_ident(id) {
                Builtin(fxn) => {
            }
            */
        } else {
            let data = Data::from_token(tok)?;
            self.data_stack.push(data);
        }
        Ok(())
    }

    fn parse<'a>(&mut self, line: &'a str) -> Result<(), LexError1<'a>> {
        for tok_or_err in tokenize(line) {
            let tok = tok_or_err?;
            self.process_token(tok);
        }

        return Ok(());
    }
}

impl std::fmt::Display for Token {
    fn fmt(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Token::Str(s) => { formatter.write_fmt(format_args!("STR \"{}\"", s)) },
            Token::Integer(i) => { formatter.write_fmt(format_args!("INT \"{}\"", i)) },
            Token::Float(f) => { formatter.write_fmt(format_args!("FLT \"{}\"", f)) },
            Token::Ident(id) => { formatter.write_fmt(format_args!("ID \"{}\"", id)) },
        }
    }
}

fn repl(prompt: &str, r: &mut std::io::BufRead, w: &mut std::io::Write) -> std::io::Result<()> {
    let mut line = String::new();

    let mut forth = ToyForth::new();

    loop {
        write!(w, "{}", prompt)?;
        w.flush()?;

        line.clear();
        r.read_line(&mut line)?;
        // println!("line is: {}", line);

        if line.is_empty() {
            break
        }

        if let Err(_err) = forth.parse(&line) {
            println!("error");
        } else {
            // print top of stack
        }
    }

    return Ok(());
}

fn main() {
    let stdin = std::io::stdin();
    let stdout = std::io::stdout();

    let mut in_handle = stdin.lock();
    let mut out_handle = stdout.lock();

    if let Err(err) = repl("> ", &mut in_handle, &mut out_handle) {
        println!("Error encountered: {}", err);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn token_as_num() {
        let v1 = "123";
        assert_eq!(LexToken::parse_num(&v1), Ok(LexToken::int(123, v1)));
        assert_ne!(LexToken::parse_num(&v1), Ok(LexToken::int(456, v1)));

        let v2 = "123.45";
        assert_eq!(LexToken::parse_num(&v2), Ok(LexToken::flt(123.45, v2)));

        let v3 = "+999";
        assert_eq!(LexToken::parse_num(&v3), Ok(LexToken::int(999, v3)));
    }

    #[test]
    fn token_as_str() {
        let v1 = "foo";
        assert_eq!(LexToken::str("foo",&v1), LexToken{token:Token::Str(v1.to_string()), source:v1});
    }

    #[test]
    fn token_as_ident() {
        let v1 = "foo";
        assert_eq!(LexToken::ident(&v1), LexToken{token:Token::Ident(v1.to_string()), source:v1});
    }

    #[test]
    fn tokens() {
        let s = "foo \"bar\" 123";
        let toks: Vec<LexToken> = tokenize(s).map(|x| x.unwrap()).collect();
        assert_eq!(toks, vec![ LexToken::ident(&s[0..3]), LexToken::str("bar", &s[5..8]), LexToken::int(123,&s[10..]) ]);
    }

    #[test]
    fn num_tokens() {
        let s = "+123 -456 12.50";
        let toks: Vec<LexToken> = tokenize(s).map(|x| x.unwrap()).collect();
        assert_eq!(toks, vec![ LexToken::int(123,&s[0..4]), LexToken::int(-456,&s[5..9]), LexToken::flt(12.50,&s[10..]) ]);
    }

    #[test]
    fn esc_strings() {
        let s = "\"foo\\n\" \"bar\\\"baz\\\"quux\" \"X\\r\\nY\"";
        let toks: Vec<LexToken> = tokenize(s).map(|x| x.unwrap()).collect();
        assert_eq!(toks, vec![
           LexToken::str("foo\n", &s[1..6]),
           LexToken::str("bar\"baz\"quux", &s[9..23]),
           LexToken::str("X\r\nY", &s[26..32])
        ]);
    }

    #[test]
    fn invalid_tokens() {
        let s = "+123a \\foo foo\\bar 12.5.0 \"unending";
        let toks: Vec<Result<LexToken,LexError1>> = tokenize(s).collect();
        assert_eq!(toks, vec![ 
            Err(LexError1{ error: LexErrorType::InvalidNumber, source: &s[0..5] }),
            Err(LexError1{ error: LexErrorType::InvalidIdent, source: &s[6..10] }),
            Err(LexError1{ error: LexErrorType::InvalidIdent, source: &s[11..18] }),
            Err(LexError1{ error: LexErrorType::InvalidNumber, source: &s[19..25] }),
            Err(LexError1{ error: LexErrorType::UnterminatedString, source: &s[27..] }),
        ]);
    }
}
