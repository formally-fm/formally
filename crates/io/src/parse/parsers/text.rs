//
// ::formally - the open-source formal methods toolchain
//
// Copyright (c) 2025 Nicola Gigante
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in
// all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.
//

use crate::parse::*;
use formally_support::*;

/// A parser accepting any character.
///
/// [any()] consumes and returns whatever character it finds in the buffer.
///
/// Combined with [only_if()](Control::only_if) allows to accept any character satisfying a given
/// predicate and reject the others. [any()] is the basic building block of most of the other
/// parsers of the library.
pub fn any() -> Parser<'static, char> {
    Parser::new(move |state: &mut State| {
        let mut saved = state.view.clone();
        match saved.next() {
            Some(ch) => {
                state.view = saved;
                Ok(ch)
            }
            None => {
                let span = Span::Span {
                    origin: state.origin.clone(),
                    begin: saved.location,
                    end: saved.location,
                };
                error!(state, span, SyntaxIssue::UnexpectedEOF);
                Err(DiagnosticEmitted.into())
            }
        }
    })
}

/// Parser that accepts if and only if the parsing position is at the end of the buffer.
pub fn eof() -> Parser<'static, ()> {
    Parser::new(move |state: &mut State| {
        let mut split = state.split();
        match split.view.next() {
            None => Ok(()),
            Some(_) => {
                let Token(token, span) = state.token();
                error!(
                    state,
                    span,
                    SyntaxIssue::Expected(
                        Name::Name {
                            singular: "EOF".to_string(),
                            plural: "EOFs".to_string(),
                        },
                        token.to_string()
                    )
                );
                Err(DiagnosticEmitted.into())
            }
        }
    })
}

/// Parser that accepts and returns only a specific character.
pub fn char(ch: char) -> Parser<'static, char> {
    any()
        .only_if(move |c| *c == ch)
        .named(format!("character '{ch}'"), format!("characters '{ch}'"))
}

/// Parser that accepts and returns only a specific string of characters.
pub fn text(txt: &str) -> Parser<'_, String> {
    foreach(txt.chars(), char).to_string().silent().named(
        format!("occurrence of \"{txt}\""),
        format!("occurrences of \"{txt}\""),
    )
}

/// Parser that accepts and returns only a specific keyword.
///
/// [keyword()] works exactly as [text()] but the error diagnostic emitted in case of rejection
/// hints at the fact that a keyword was expected.
pub fn keyword(kw: &str) -> Parser<'_, String> {
    text(kw).named(format!("keyword \"{kw}\""), format!("keywords \"{kw}\""))
}

/// Parser that accepts only alphabetic characters (as tested by [char::is_alphabetic]).
pub fn alphabetic() -> Parser<'static, char> {
    any()
        .only_if(|c| c.is_alphabetic())
        .named("alphabetic character", "alphabetic characters")
}

/// Parser that accepts only alphanumeric characters (as tested by [char::is_alphanumeric]).
pub fn alphanumeric() -> Parser<'static, char> {
    any()
        .only_if(|c| c.is_alphanumeric())
        .named("alphanumeric character", "alphanumeric characters")
}

/// Parser that accepts only base-n digits for the given `radix` (as tested by [char::is_digit]).
pub fn digit(radix: u32) -> Parser<'static, char> {
    any().only_if(move |c| c.is_digit(radix)).named(
        format!("base-{radix} digit"),
        format!("base-{radix} digits"),
    )
}

/// Parser that accepts only lowercase characters (as tested by [char::is_lowercase]).
pub fn lowercase() -> Parser<'static, char> {
    any()
        .only_if(|c| c.is_lowercase())
        .named("lowercase character", "lowercase characters")
}

/// Parser that accepts only base-10 numeric characters (as tested by [char::is_lowercase]).
pub fn numeric() -> Parser<'static, char> {
    any().only_if(|c| c.is_numeric()).named("digit", "digits")
}

/// Parser that accepts only uppercase characters (as tested by [char::is_uppercase]).
pub fn uppercase() -> Parser<'static, char> {
    any()
        .only_if(|c| c.is_uppercase())
        .named("uppercase character", "uppercase characters")
}

/// Parser that accepts only whitespace characters (as tested by [char::is_whitespace]).
pub fn whitespace() -> Parser<'static, char> {
    any()
        .only_if(|c| c.is_whitespace())
        .named("whitespace character", "whitespace characters")
}

/// Parser that accepts only ascii characters (as tested by [char::is_ascii]).
pub fn ascii() -> Parser<'static, char> {
    any()
        .only_if(|c| c.is_ascii())
        .named("ascii character", "ascii characters")
}

/// Parser that accepts only ascii alphabetic characters (as tested by [char::is_ascii_alphabetic]).
pub fn ascii_alphabetic() -> Parser<'static, char> {
    any()
        .only_if(|c| c.is_ascii_alphabetic())
        .named("ascii alphabetic character", "ascii alphabetic characters")
}

/// Parser that accepts only ascii alphanumeric characters (as tested by
/// [char::is_ascii_alphanumeric]).
pub fn ascii_alphanumeric() -> Parser<'static, char> {
    any().only_if(|c| c.is_ascii_alphanumeric()).named(
        "ascii alphanumeric character",
        "ascii alphanumeric characters",
    )
}

/// Parser that accepts only ascii base-10 digit characters (as tested by [char::is_ascii_digit]).
pub fn ascii_digit() -> Parser<'static, char> {
    any()
        .only_if(|c| c.is_ascii_digit())
        .named("ascii digit", "ascii digits")
}

/// Parser that accepts only ascii graphic characters (as tested by [char::is_ascii_graphic]).
pub fn ascii_graphic() -> Parser<'static, char> {
    any()
        .only_if(|c| c.is_ascii_graphic())
        .named("ascii graphic character", "ascii graphic characters")
}

/// Parser that accepts only ascii hexadecimal digit characters (as tested by
/// [char::is_ascii_hexdigit]).
pub fn ascii_hexdigit() -> Parser<'static, char> {
    any()
        .only_if(|c| c.is_ascii_hexdigit())
        .named("ascii hexadecimal digit", "ascii graphic characters")
}

/// Parser that accepts only binary digit characters (i.e., either '0' or '1').
pub fn ascii_binary_digit() -> Parser<'static, char> {
    any()
        .only_if(|c| *c == '0' || *c == '1')
        .named("binary digit", "binary digits")
}

/// Parser that accepts only ascii lowercase characters (as tested by [char::is_ascii_lowercase]).
pub fn ascii_lowercase() -> Parser<'static, char> {
    any()
        .only_if(|c| c.is_ascii_lowercase())
        .named("ascii lowercase character", "ascii lowercase character")
}

/// Parser that accepts only ascii punctuation characters (as tested by
/// [char::is_ascii_punctuation]).
pub fn ascii_punctuation() -> Parser<'static, char> {
    any().only_if(|c| c.is_ascii_punctuation()).named(
        "ascii punctuation character",
        "ascii punctuation characters",
    )
}

/// Parser that accepts only ascii uppercase characters (as tested by [char::is_ascii_uppercase]).
pub fn ascii_uppercase() -> Parser<'static, char> {
    any()
        .only_if(|c| c.is_ascii_uppercase())
        .named("ascii uppercase character", "ascii uppercase character")
}

/// Parser that accepts only ascii whitespace characters (as tested by [char::is_ascii_whitespace]).
pub fn ascii_whitespace() -> Parser<'static, char> {
    any()
        .only_if(|c| c.is_ascii_whitespace())
        .named("ascii whitespace character", "ascii whitespace character")
}
