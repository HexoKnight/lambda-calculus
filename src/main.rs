use console::Term;
use std::{fmt::{Write, Display}, collections::HashMap};
use itertools::Itertools;

use LambdaExpressionParseError as LEPE;
#[derive(Debug)]
struct LambdaExpressionParseError {
    pub description: &'static str,
    pub start_index: usize,
    pub end_index: usize,
}
impl LEPE {
    pub fn new(description: &'static str, start_index: usize, end_index: usize) -> Self {
        Self { description, start_index, end_index }
    }

    pub fn to_str(&self, source_offset: usize) -> String {
        let mut full = String::new();
        full.extend(std::iter::repeat(' ').take(source_offset + self.start_index));
        full += "^";
        if self.end_index > self.start_index {
            full.extend(std::iter::repeat('-').take(self.end_index - self.start_index - 1));
            full += "^";
        }
        else if self.end_index < self.start_index {
            full += "-----...";
        }
        full += "\n";
        full += self.description;
        full
    }
}
impl Display for LEPE {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_str(0))
    }
}

#[derive(Clone)]
enum LambdaExpression {
    Function(char, Box<LambdaExpression>),
    Application(Box<LambdaExpression>, Box<LambdaExpression>),
    Variable(char),
}
impl Default for LambdaExpression {
    fn default() -> Self {
        Self::Variable('\\') // shouldn't be constructable in normal means
    }
}
impl Display for LambdaExpression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Function(var, body) => {
                write!(f, "λ{var}.{body}")
            }
            Self::Application(function, input) => {
                let function_str = if matches!(**function, Self::Function(_, _)) {
                    format!("({function})")
                }
                else {
                    function.to_string()
                };
                let input_str = if matches!(**input, Self::Application(_, _)|Self::Function(_, _)) {
                    format!("({input})")
                }
                else {
                    input.to_string()
                };

                write!(f, "{function_str} {input_str}")
            }
            Self::Variable(chr) => f.write_char(*chr),
        }
    }
}
impl LambdaExpression {

    pub fn parse(string: &str) -> Result<Self, LEPE> {
        Self::parse_recursive(string.char_indices(), None)
    }
    fn parse_unsanitised(indexed_char_vec: Vec<(usize, char)>) -> Result<Self, LEPE> {
        if indexed_char_vec.len() == 0 {
            return Err(LEPE::new("empty expression: unknown position :(", 0, 0))
        }
        let mut start: usize = 0;
        let mut end: usize = indexed_char_vec.len() - 1;

        while start <= end && match (indexed_char_vec[start].1, indexed_char_vec[end].1) {
            ('(', ')') => { start += 1; end -= 1; true }
            (s, _) if s.is_whitespace() => { start += 1; true }
            (_, e) if e.is_whitespace() => { end -= 1; true }
            (_, _) => false
        } {}
        if start > end {
            return Err(LEPE::new("empty expression", indexed_char_vec[0].0, indexed_char_vec[indexed_char_vec.len() - 1].0))
        }

        //let final_sanitised: String = char_vec[start..end + 1].iter().collect();

        if indexed_char_vec[start].1 == '\\' || indexed_char_vec[start..end + 1].iter().any(|c| c.1.is_whitespace() || c.1 == '(' || c.1 == ')') {
            Self::parse_recursive(indexed_char_vec[start..end + 1].to_owned().into_iter(), None)
        }
        else if start == end {
            Ok(Self::Variable(indexed_char_vec[start].1))
        }
        else {
            Err(LEPE::new("global bindings not implemented", indexed_char_vec[start].0, indexed_char_vec[end].0))
        }
    }
    fn parse_recursive(char_iter: impl IntoIterator<Item=(usize, char)>, mut function_start_next_char: Option<(usize, char)>) -> Result<Self, LEPE> {
        let mut char_iter = char_iter.into_iter();

        while function_start_next_char.is_some_and(|c| c.1.is_whitespace()) {
            function_start_next_char = Some(char_iter.next().ok_or_else(|| LEPE::new("Unexpected end of abstraction", 0, 0))?);
        }

        let mut chr: Option<(usize, char)> = None;
        while {
            chr = Some(char_iter.next().ok_or_else(|| 
                LEPE::new("Unexpected end of expression", chr.unwrap_or((0, ' ')).0 + 1, chr.unwrap_or((0, ' ')).0 + 1))?);
            chr.unwrap().1.is_whitespace()
        } {}
        let chr = chr.unwrap();

        if chr.1 == '\\' || function_start_next_char.is_some_and(|c| c.1 != '.' ) {
            let var = function_start_next_char.or_else(|| char_iter.next())
                .ok_or_else(|| LEPE::new("Unexpected end of abstraction", chr.0 + 1, chr.0 + 1))?;
            let next_char = if function_start_next_char.is_some() {
                chr
            } else {
                char_iter.next().ok_or_else(|| LEPE::new("Unexpected end of abstraction", var.0 + 1, var.0 + 1))?
            };
            return Ok(Self::Function(
                var.1,
                Box::from(Self::parse_recursive(char_iter, Some(next_char))?)
            ))
        }
        
        let mut bracket_level = 0;
        let total_groups = std::iter::once(chr).chain(char_iter).group_by(|c|
            match c.1 {
                '(' => {
                    bracket_level += 1;
                    bracket_level > 1
                }
                ')' => {
                    bracket_level -= 1;
                    bracket_level > 0
                }
                c => bracket_level > 0 || !c.is_whitespace()
            }
        );
        let mut applications = total_groups.into_iter().filter_map(|(is_expr, expr)| {
            if is_expr {
                Some(expr)
            } else {
                None
            }
        });

        let first_expr: _ = applications.next().ok_or_else(|| LEPE::new("empty expression", chr.0, 0))?;
        let mut previous_expr = Self::parse_unsanitised(first_expr.collect_vec())?;
        while let Some(next_expr) = applications.next() {
            previous_expr = Self::Application(
                Box::from(previous_expr),
                Box::from(Self::parse_unsanitised(next_expr.collect())?)
            );
        }
        Ok(previous_expr)
    }

    fn b_reduce(self, recursive: bool) -> (Self, bool) {
        let (new_self, _, b_reduced) = Box::new(self).b_reduce_recursive(HashMap::new(), recursive, true, 0);
        (*new_self, b_reduced)
    }
    fn b_reduce_recursive(mut self: Box<Self>, mut replacements: HashMap<char, LambdaExpression>, recursive: bool, b_reduce: bool, depth: u32)
    -> (Box<Self>, HashMap<char, LambdaExpression>, bool) {
        // #[cfg(debug_assertions)]
        // if !matches!(*self, Self::Variable(_)) {
        //     println!("{depth}: {self}");
        // }
        match *self {
            Self::Function(var, mut body) => {
                let prev = replacements.remove(&var);
                let b_reduced;
                (body, replacements, b_reduced) = body.b_reduce_recursive(replacements, recursive, b_reduce, depth + 1);
                if let Some(prev_expr) = prev {
                    replacements.insert(var, prev_expr);
                }
                (Box::from(Self::Function(var, body)), replacements, b_reduced)
            }
            Self::Application(mut function, mut input) => {
                if recursive {
                    (function, replacements, _) = function.b_reduce_recursive(replacements, recursive, b_reduce, depth + 1);
                }
                match *function {
                    Self::Function(var, mut body) => {
                        (input, replacements, _) = input.b_reduce_recursive(replacements, recursive, false, depth + 1); // do not b_reduce right to avoid loop

                        if b_reduce {
                            let prev = replacements.insert(var, *input);
                            (body, replacements, _) = body.b_reduce_recursive(replacements, recursive, b_reduce, depth + 1);
                            if let Some(prev_var) = prev {
                                replacements.insert(var, prev_var);
                            } else {
                                replacements.remove(&var);
                            }
                            (body, replacements, true)
                        } else {
                            (Box::from(Self::Function(var, body)), replacements, false)
                        }
                    }
                    _ => {
                        let mut b_reduced = false;
                        if !recursive {
                            (function, replacements, b_reduced) = function.b_reduce_recursive(replacements, recursive, b_reduce, depth + 1);
                            if !b_reduced {
                                (input, replacements, b_reduced) = input.b_reduce_recursive(replacements, recursive, b_reduce, depth + 1);
                            }
                        }
                        (Box::from(Self::Application(function, input)), replacements, b_reduced)
                    }
                }
            }
            Self::Variable(c) => {
                if let Some(expr) = replacements.get(&c) {
                    self = Box::from(expr.clone());
                }
                (self, replacements, false)
            }
        }
    }
}

fn main() {
    let k = LambdaExpression::parse("\\xy.x").unwrap();
    let s = LambdaExpression::parse("\\xyz.x z (y z)").unwrap();
    
    println!("K combinator: {}", k);
    println!("S combinator: {}", s);

    println!("Enter lambda expressions to parse and reduce (empty to stop):");

    let mut out: String;
    while {
        print!("> ");
        std::io::Write::flush(&mut std::io::stdout()).unwrap();
        out = Term::stdout().read_line().unwrap_or_default();
        !out.is_empty()
    } {
        match LambdaExpression::parse(&out) {
            Ok(mut expr) => {
                println!("{expr}");
                let mut b_reduced;
                while {
                    (expr, b_reduced) = expr.b_reduce(false);
                    b_reduced
                } {
                    println!("{}", expr);
                }
            }
            Err(err) => println!("{}", err.to_str(2)), // 2 offset is from '> ' in input
        }
    }
}
