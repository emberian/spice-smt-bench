//! Zero-dependency parser for extended SPICE + Multi-PDK + PCB + TCAD `.sp` decks.

use std::collections::BTreeMap;

use crate::ast::{
    AnalysisMode, BoundDecl, CmpOp, Deck, Element, ExpectedStatus, Expr, Formula, InitDecl,
    InitSpec, ModelDecl, ModelKind, ParamDecl, TranMethod, Waveform,
};
use crate::pdk::PdkId;

/// Parse an engineering floating-point literal (`10k`, `22u`, `15p`, `0.85`, `1.2e13`).
pub fn parse_spice_number(raw: &str) -> Result<f64, String> {
    let s = raw.trim();
    if s.is_empty() {
        return Err("empty numeric literal".to_string());
    }
    if let Ok(v) = s.parse::<f64>() {
        return Ok(v);
    }
    let lower = s.to_ascii_lowercase();
    let suffixes: &[(&str, f64)] = &[
        ("meg", 1e6),
        ("mil", 25.4e-6),
        ("t", 1e12),
        ("g", 1e9),
        ("k", 1e3),
        ("m", 1e-3),
        ("u", 1e-6),
        ("n", 1e-9),
        ("p", 1e-12),
        ("f", 1e-15),
    ];
    for (suf, scale) in suffixes {
        if let Some(prefix) = lower.strip_suffix(suf) {
            if let Ok(base) = prefix.trim().parse::<f64>() {
                return Ok(base * scale);
            }
        }
    }
    Err(format!("invalid SPICE number `{raw}`"))
}

#[derive(Debug, Clone, PartialEq)]
enum Tok {
    Num(f64),
    Ident(String),
    LParen,
    RParen,
    Plus,
    Minus,
    Star,
    Slash,
    AndAnd,
    OrOr,
    Bang,
    EqEq,
    Lt,
    Le,
    Gt,
    Ge,
}

fn tokenize_expr(input: &str) -> Result<Vec<Tok>, String> {
    let bytes = input.as_bytes();
    let mut i = 0;
    let mut out = Vec::new();
    while i < bytes.len() {
        let ch = bytes[i] as char;
        if ch.is_ascii_whitespace() {
            i += 1;
            continue;
        }
        match ch {
            '(' => {
                out.push(Tok::LParen);
                i += 1;
            }
            ')' => {
                out.push(Tok::RParen);
                i += 1;
            }
            '+' => {
                out.push(Tok::Plus);
                i += 1;
            }
            '-' => {
                out.push(Tok::Minus);
                i += 1;
            }
            '*' => {
                out.push(Tok::Star);
                i += 1;
            }
            '/' => {
                out.push(Tok::Slash);
                i += 1;
            }
            '&' => {
                if i + 1 < bytes.len() && bytes[i + 1] == b'&' {
                    out.push(Tok::AndAnd);
                    i += 2;
                } else {
                    return Err("expected `&&` in formula".to_string());
                }
            }
            '|' => {
                if i + 1 < bytes.len() && bytes[i + 1] == b'|' {
                    out.push(Tok::OrOr);
                    i += 2;
                } else {
                    return Err("expected `||` in formula".to_string());
                }
            }
            '!' => {
                out.push(Tok::Bang);
                i += 1;
            }
            '=' => {
                if i + 1 < bytes.len() && bytes[i + 1] == b'=' {
                    out.push(Tok::EqEq);
                    i += 2;
                } else {
                    out.push(Tok::EqEq);
                    i += 1;
                }
            }
            '<' => {
                if i + 1 < bytes.len() && bytes[i + 1] == b'=' {
                    out.push(Tok::Le);
                    i += 2;
                } else {
                    out.push(Tok::Lt);
                    i += 1;
                }
            }
            '>' => {
                if i + 1 < bytes.len() && bytes[i + 1] == b'=' {
                    out.push(Tok::Ge);
                    i += 2;
                } else {
                    out.push(Tok::Gt);
                    i += 1;
                }
            }
            _ if ch.is_ascii_digit() || ch == '.' => {
                let start = i;
                i += 1;
                while i < bytes.len() {
                    let c = bytes[i] as char;
                    if c.is_ascii_digit() || c == '.' {
                        i += 1;
                    } else if (c == 'e' || c == 'E') && i + 1 < bytes.len() {
                        let next = bytes[i + 1] as char;
                        if next.is_ascii_digit() || next == '+' || next == '-' {
                            i += 2;
                            while i < bytes.len() && (bytes[i] as char).is_ascii_digit() {
                                i += 1;
                            }
                        } else {
                            break;
                        }
                    } else if c.is_ascii_alphabetic() {
                        i += 1;
                    } else {
                        break;
                    }
                }
                let lit = &input[start..i];
                let num = parse_spice_number(lit)?;
                out.push(Tok::Num(num));
            }
            _ if ch.is_ascii_alphabetic() || ch == '_' => {
                let start = i;
                i += 1;
                while i < bytes.len() {
                    let c = bytes[i] as char;
                    if c.is_ascii_alphanumeric() || c == '_' {
                        i += 1;
                    } else {
                        break;
                    }
                }
                out.push(Tok::Ident(input[start..i].to_string()));
            }
            _ => {
                return Err(format!("unexpected character `{ch}` in `{input}`"));
            }
        }
    }
    Ok(out)
}

struct ExprParser {
    toks: Vec<Tok>,
    pos: usize,
}

impl ExprParser {
    fn new(toks: Vec<Tok>) -> Self {
        Self { toks, pos: 0 }
    }

    fn peek(&self) -> Option<&Tok> {
        self.toks.get(self.pos)
    }

    fn next(&mut self) -> Option<Tok> {
        let t = self.toks.get(self.pos).cloned();
        if t.is_some() {
            self.pos += 1;
        }
        t
    }

    fn expect_rparen(&mut self) -> Result<(), String> {
        match self.next() {
            Some(Tok::RParen) => Ok(()),
            other => Err(format!("expected `)`, found `{other:?}`")),
        }
    }

    fn parse_formula(&mut self) -> Result<Formula, String> {
        self.parse_or()
    }

    fn parse_or(&mut self) -> Result<Formula, String> {
        let mut items = vec![self.parse_and()?];
        while matches!(self.peek(), Some(Tok::OrOr)) {
            self.next();
            items.push(self.parse_and()?);
        }
        if items.len() == 1 {
            Ok(items.pop().unwrap())
        } else {
            Ok(Formula::Or(items))
        }
    }

    fn parse_and(&mut self) -> Result<Formula, String> {
        let mut items = vec![self.parse_unary_formula()?];
        while matches!(self.peek(), Some(Tok::AndAnd)) {
            self.next();
            items.push(self.parse_unary_formula()?);
        }
        if items.len() == 1 {
            Ok(items.pop().unwrap())
        } else {
            Ok(Formula::And(items))
        }
    }

    fn parse_unary_formula(&mut self) -> Result<Formula, String> {
        if matches!(self.peek(), Some(Tok::Bang)) {
            self.next();
            return Ok(Formula::Not(Box::new(self.parse_unary_formula()?)));
        }
        if matches!(self.peek(), Some(Tok::LParen)) {
            let save = self.pos;
            self.next();
            if let Ok(f) = self.parse_formula() {
                if matches!(self.peek(), Some(Tok::RParen)) {
                    self.next();
                    if !matches!(
                        self.peek(),
                        Some(
                            Tok::Plus
                                | Tok::Minus
                                | Tok::Star
                                | Tok::Slash
                                | Tok::EqEq
                                | Tok::Lt
                                | Tok::Le
                                | Tok::Gt
                                | Tok::Ge
                        )
                    ) {
                        return Ok(f);
                    }
                }
            }
            self.pos = save;
        }
        let lhs = self.parse_expr()?;
        let op = match self.next() {
            Some(Tok::EqEq) => CmpOp::Eq,
            Some(Tok::Lt) => CmpOp::Lt,
            Some(Tok::Le) => CmpOp::Le,
            Some(Tok::Gt) => CmpOp::Gt,
            Some(Tok::Ge) => CmpOp::Ge,
            other => return Err(format!("expected comparison operator, found `{other:?}`")),
        };
        let rhs = self.parse_expr()?;
        Ok(Formula::Cmp { op, lhs, rhs })
    }

    fn parse_expr(&mut self) -> Result<Expr, String> {
        let mut acc = self.parse_term()?;
        loop {
            match self.peek() {
                Some(Tok::Plus) => {
                    self.next();
                    acc = Expr::add(acc, self.parse_term()?);
                }
                Some(Tok::Minus) => {
                    self.next();
                    acc = Expr::sub(acc, self.parse_term()?);
                }
                _ => break,
            }
        }
        Ok(acc)
    }

    fn parse_term(&mut self) -> Result<Expr, String> {
        let mut acc = self.parse_unary()?;
        loop {
            match self.peek() {
                Some(Tok::Star) => {
                    self.next();
                    acc = Expr::mul(acc, self.parse_unary()?);
                }
                Some(Tok::Slash) => {
                    self.next();
                    acc = Expr::div(acc, self.parse_unary()?);
                }
                _ => break,
            }
        }
        Ok(acc)
    }

    fn parse_unary(&mut self) -> Result<Expr, String> {
        match self.peek() {
            Some(Tok::Minus) => {
                self.next();
                Ok(Expr::neg(self.parse_unary()?))
            }
            Some(Tok::Plus) => {
                self.next();
                self.parse_unary()
            }
            _ => self.parse_primary(),
        }
    }

    fn parse_primary(&mut self) -> Result<Expr, String> {
        match self.next() {
            Some(Tok::Num(v)) => Ok(Expr::Num(v)),
            Some(Tok::LParen) => {
                let inner = self.parse_expr()?;
                self.expect_rparen()?;
                Ok(inner)
            }
            Some(Tok::Ident(id)) => {
                if matches!(self.peek(), Some(Tok::LParen)) {
                    self.next();
                    let lower = id.to_ascii_lowercase();
                    if lower == "v" {
                        let node_tok = self.next();
                        let node_name = match node_tok {
                            Some(Tok::Ident(n)) => n,
                            Some(Tok::Num(0.0)) => "0".to_string(),
                            other => {
                                return Err(format!("invalid node inside v(...): `{other:?}`"))
                            }
                        };
                        self.expect_rparen()?;
                        Ok(Expr::node(node_name))
                    } else if lower == "exp" {
                        let arg = self.parse_expr()?;
                        self.expect_rparen()?;
                        Ok(Expr::exp(arg))
                    } else if lower == "ln1p_exp" || lower == "softplus" {
                        let arg = self.parse_expr()?;
                        self.expect_rparen()?;
                        Ok(Expr::ln1p_exp(arg))
                    } else if lower == "sq" {
                        let arg = self.parse_expr()?;
                        self.expect_rparen()?;
                        Ok(Expr::sq(arg))
                    } else {
                        Err(format!("unknown function `{id}(...)`"))
                    }
                } else if id == "t" || id == "time" {
                    Ok(Expr::Time)
                } else {
                    Ok(Expr::Var(id))
                }
            }
            other => Err(format!("unexpected token `{other:?}` in expression")),
        }
    }
}

/// Parse a real-valued expression string (with or without enclosing `{...}`).
pub fn parse_expr_str(raw: &str) -> Result<Expr, String> {
    let trimmed = raw.trim();
    let inner = if let Some(s) = trimmed.strip_prefix('{').and_then(|s| s.strip_suffix('}')) {
        s.trim()
    } else {
        trimmed
    };
    if let Ok(num) = parse_spice_number(inner) {
        return Ok(Expr::Num(num));
    }
    let toks = tokenize_expr(inner)?;
    let mut parser = ExprParser::new(toks);
    let expr = parser.parse_expr()?;
    if parser.pos != parser.toks.len() {
        return Err(format!(
            "trailing tokens in expression `{raw}` starting at {:?}",
            parser.toks[parser.pos]
        ));
    }
    Ok(expr)
}

/// Parse a quantifier-free boolean formula string.
pub fn parse_formula_str(raw: &str) -> Result<Formula, String> {
    let toks = tokenize_expr(raw.trim())?;
    let mut parser = ExprParser::new(toks);
    let f = parser.parse_formula()?;
    if parser.pos != parser.toks.len() {
        return Err(format!(
            "trailing tokens in formula `{raw}` starting at {:?}",
            parser.toks[parser.pos]
        ));
    }
    Ok(f)
}

/// Split a SPICE line into tokens while keeping `{...}` and `(...)` groups intact.
fn split_spice_tokens(line: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut cur = String::new();
    let mut brace_depth = 0usize;
    let mut paren_depth = 0usize;
    for ch in line.chars() {
        match ch {
            '{' => {
                brace_depth += 1;
                cur.push(ch);
            }
            '}' => {
                brace_depth = brace_depth.saturating_sub(1);
                cur.push(ch);
            }
            '(' => {
                paren_depth += 1;
                cur.push(ch);
            }
            ')' => {
                paren_depth = paren_depth.saturating_sub(1);
                cur.push(ch);
            }
            c if c.is_ascii_whitespace() && brace_depth == 0 && paren_depth == 0 => {
                if !cur.is_empty() {
                    out.push(std::mem::take(&mut cur));
                }
            }
            _ => cur.push(ch),
        }
    }
    if !cur.is_empty() {
        out.push(cur);
    }
    out
}

fn parse_bracket_interval(raw: &str) -> Result<(f64, f64), String> {
    let s = raw.trim();
    let inner = s
        .strip_prefix('[')
        .and_then(|x| x.strip_suffix(']'))
        .ok_or_else(|| format!("expected interval `[lo, hi]`, got `{raw}`"))?;
    let parts: Vec<&str> = inner.split(',').collect();
    if parts.len() != 2 {
        return Err(format!("expected two bounds in `[lo, hi]`, got `{raw}`"));
    }
    let lo = parse_spice_number(parts[0])?;
    let hi = parse_spice_number(parts[1])?;
    if lo > hi {
        return Err(format!("interval lower bound {lo} > upper bound {hi}"));
    }
    Ok((lo, hi))
}

fn parse_kv_tokens(tokens: &[String]) -> Result<BTreeMap<String, Expr>, String> {
    let mut map = BTreeMap::new();
    for tok in tokens {
        let t = tok.trim();
        let clean = t
            .strip_prefix('(')
            .unwrap_or(t)
            .strip_suffix(')')
            .unwrap_or(t);
        for piece in split_spice_tokens(clean) {
            if piece.is_empty() {
                continue;
            }
            if let Some((k, v)) = piece.split_once('=') {
                map.insert(k.trim().to_ascii_lowercase(), parse_expr_str(v.trim())?);
            } else {
                return Err(format!("expected `key=value`, got `{piece}`"));
            }
        }
    }
    Ok(map)
}

fn get_req_expr(
    kvs: &BTreeMap<String, Expr>,
    key: &str,
    ctx: &str,
) -> Result<Expr, String> {
    kvs.get(key)
        .cloned()
        .ok_or_else(|| format!("missing required parameter `{key}` in {ctx}"))
}

fn get_req_f64(kvs: &BTreeMap<String, Expr>, key: &str, ctx: &str) -> Result<f64, String> {
    match get_req_expr(kvs, key, ctx)? {
        Expr::Num(v) => Ok(v),
        other => Err(format!(
            "parameter `{key}` in {ctx} must be a constant number, got `{other:?}`"
        )),
    }
}

fn parse_waveform(tokens: &[String]) -> Result<Waveform, String> {
    if tokens.is_empty() {
        return Err("missing source waveform".to_string());
    }
    let head_upper = tokens[0].to_ascii_uppercase();
    if head_upper == "DC" {
        if tokens.len() < 2 {
            return Err("expected value after `DC`".to_string());
        }
        return Ok(Waveform::Dc(parse_expr_str(&tokens[1])?));
    }
    let joined = tokens.join(" ");
    if let Some(rest) = joined
        .strip_prefix("GAUSS(")
        .or_else(|| joined.strip_prefix("gauss("))
        .and_then(|s| s.strip_suffix(')'))
    {
        let kvs = parse_kv_tokens(&split_spice_tokens(rest))?;
        return Ok(Waveform::GaussPulse {
            base: kvs.get("base").cloned().unwrap_or_else(|| Expr::num(0.0)),
            amp: get_req_expr(&kvs, "amp", "GAUSS waveform")?,
            t0: get_req_expr(&kvs, "t0", "GAUSS waveform")?,
            width: get_req_expr(&kvs, "width", "GAUSS waveform")?,
        });
    }
    if let Some(rest) = joined
        .strip_prefix("STEP(")
        .or_else(|| joined.strip_prefix("step("))
        .and_then(|s| s.strip_suffix(')'))
    {
        let kvs = parse_kv_tokens(&split_spice_tokens(rest))?;
        return Ok(Waveform::SmoothStep {
            base: kvs.get("base").cloned().unwrap_or_else(|| Expr::num(0.0)),
            step: get_req_expr(&kvs, "step", "STEP waveform")?,
            t0: get_req_expr(&kvs, "t0", "STEP waveform")?,
            tau: get_req_expr(&kvs, "tau", "STEP waveform")?,
        });
    }
    Ok(Waveform::Dc(parse_expr_str(&tokens[0])?))
}

fn normalize_bound_target(raw: &str) -> String {
    let t = raw.trim();
    if let Some(inner) = t
        .strip_prefix("v(")
        .or_else(|| t.strip_prefix("V("))
        .and_then(|s| s.strip_suffix(')'))
    {
        format!("v_{}", crate::ast::sanitize_ident(inner.trim()))
    } else {
        t.to_string()
    }
}

/// Apply built-in PDK models into `deck` without overwriting user-supplied `.model` cards.
pub fn apply_pdk_defaults(deck: &mut Deck, pdk: PdkId) {
    deck.pdk = Some(pdk);
    let profile = pdk.profile();
    for m in profile.default_models {
        deck.models.entry(m.name.clone()).or_insert(m);
    }
}

/// Parse a complete `.sp` netlist / multiphysics verification deck.
pub fn parse_deck(source: &str) -> Result<Deck, String> {
    let mut logical_lines: Vec<(usize, String)> = Vec::new();
    let mut title = String::from("Untitled SPICE-SMT Deck");
    let mut saw_first_line = false;

    for (idx, raw_line) in source.lines().enumerate() {
        let line_no = idx + 1;
        let trimmed = raw_line.trim();
        if !saw_first_line && !trimmed.is_empty() {
            saw_first_line = true;
            if let Some(rest) = trimmed.strip_prefix('*') {
                let candidate = rest.trim();
                if !candidate.is_empty() {
                    title = candidate.to_string();
                }
                continue;
            }
        }
        if trimmed.is_empty() || trimmed.starts_with('*') || trimmed.starts_with(';') {
            continue;
        }
        let no_comment = match trimmed.find(';') {
            Some(pos) => trimmed[..pos].trim(),
            None => trimmed,
        };
        if no_comment.is_empty() {
            continue;
        }
        if let Some(cont) = no_comment.strip_prefix('+') {
            if let Some((_, prev)) = logical_lines.last_mut() {
                prev.push(' ');
                prev.push_str(cont.trim());
            } else {
                return Err(format!("line {line_no}: unexpected continuation `+`"));
            }
        } else {
            logical_lines.push((line_no, no_comment.to_string()));
        }
    }

    let mut deck = Deck::new(title);

    for (line_no, line) in logical_lines {
        let err_ctx = |msg: String| format!("line {line_no}: {msg}");
        if line.to_ascii_lowercase().starts_with(".end") {
            break;
        }
        if let Some(rest) = line.strip_prefix(".title").or_else(|| line.strip_prefix(".TITLE")) {
            deck.title = rest.trim().to_string();
            continue;
        }
        if let Some(rest) = line.strip_prefix(".unsafe").or_else(|| line.strip_prefix(".UNSAFE")) {
            let f = parse_formula_str(rest.trim()).map_err(err_ctx)?;
            deck.unsafe_formula = Some(match deck.unsafe_formula.take() {
                None => f,
                Some(Formula::Or(mut items)) => {
                    items.push(f);
                    Formula::Or(items)
                }
                Some(prev) => Formula::Or(vec![prev, f]),
            });
            continue;
        }
        if let Some(rest) = line.strip_prefix(".const").or_else(|| line.strip_prefix(".CONST")) {
            let (lhs, rhs) = rest
                .split_once('=')
                .ok_or_else(|| err_ctx("expected `.const <name> = <expr>`".to_string()))?;
            deck.consts.push((
                lhs.trim().to_string(),
                parse_expr_str(rhs.trim()).map_err(err_ctx)?,
            ));
            continue;
        }

        let toks = split_spice_tokens(&line);
        if toks.is_empty() {
            continue;
        }
        let head = toks[0].as_str();
        let head_lower = head.to_ascii_lowercase();

        if head_lower.starts_with('.') {
            match head_lower.as_str() {
                ".pdk" => {
                    if toks.len() != 2 {
                        return Err(err_ctx("expected `.pdk <profile>`".to_string()));
                    }
                    let pdk = PdkId::parse(&toks[1]).ok_or_else(|| {
                        err_ctx(format!(
                            "unknown PDK `{}` (supported: asap7, gt2n, ihp_sg13g2, gan_sic, gf180mcu, sky130)",
                            toks[1]
                        ))
                    })?;
                    apply_pdk_defaults(&mut deck, pdk);
                }
                ".expected" => {
                    if toks.len() != 2 {
                        return Err(err_ctx("expected `.expected sat|unsat`".to_string()));
                    }
                    deck.expected = Some(match toks[1].to_ascii_lowercase().as_str() {
                        "sat" => ExpectedStatus::Sat,
                        "unsat" => ExpectedStatus::Unsat,
                        other => {
                            return Err(err_ctx(format!("invalid `.expected {other}`")));
                        }
                    });
                }
                ".default_vbound" => {
                    let joined = toks[1..].join("");
                    deck.default_vbound = parse_bracket_interval(&joined).map_err(err_ctx)?;
                }
                ".mode" => {
                    if toks.len() < 2 {
                        return Err(err_ctx("expected `.mode dc` or `.mode tran ...`".to_string()));
                    }
                    match toks[1].to_ascii_lowercase().as_str() {
                        "dc" => deck.mode = AnalysisMode::Dc,
                        "tran" => {
                            let kvs = parse_kv_tokens(&toks[2..]).map_err(err_ctx)?;
                            let dt = get_req_f64(&kvs, "dt", ".mode tran").map_err(err_ctx)?;
                            let steps = get_req_f64(&kvs, "steps", ".mode tran").map_err(err_ctx)?
                                as usize;
                            let method = if line.to_ascii_lowercase().contains("method=trap") {
                                TranMethod::Trapezoidal
                            } else {
                                TranMethod::BackwardEuler
                            };
                            deck.mode = AnalysisMode::Tran { dt, steps, method };
                        }
                        other => return Err(err_ctx(format!("unknown mode `{other}`"))),
                    }
                }
                ".param" => {
                    if toks.len() < 3 {
                        return Err(err_ctx("expected `.param <name> [lo, hi]`".to_string()));
                    }
                    let name = toks[1].clone();
                    let interval_str = toks[2..].join("");
                    let (lo, hi) = parse_bracket_interval(&interval_str).map_err(err_ctx)?;
                    deck.params.push(ParamDecl { name, lo, hi });
                }
                ".bound" => {
                    if toks.len() < 3 {
                        return Err(err_ctx("expected `.bound <target> [lo, hi]`".to_string()));
                    }
                    let target = normalize_bound_target(&toks[1]);
                    let interval_str = toks[2..].join("");
                    let (lo, hi) = parse_bracket_interval(&interval_str).map_err(err_ctx)?;
                    deck.bounds.push(BoundDecl { target, lo, hi });
                }
                ".init" => {
                    if toks.len() < 3 {
                        return Err(err_ctx(
                            "expected `.init <target> [lo, hi]` or `.init <target> = <expr>`"
                                .to_string(),
                        ));
                    }
                    let target = normalize_bound_target(&toks[1]);
                    let rest = toks[2..].join(" ");
                    let spec = if let Some(eq_rhs) = rest.strip_prefix('=') {
                        InitSpec::Exact(parse_expr_str(eq_rhs).map_err(err_ctx)?)
                    } else {
                        let (lo, hi) =
                            parse_bracket_interval(&toks[2..].join("")).map_err(err_ctx)?;
                        InitSpec::Interval(lo, hi)
                    };
                    deck.inits.push(InitDecl { target, spec });
                }
                ".model" => {
                    if toks.len() < 3 {
                        return Err(err_ctx(
                            "expected `.model <name> <kind> (params...)`".to_string(),
                        ));
                    }
                    let name = toks[1].clone();
                    let kind = match toks[2].to_ascii_uppercase().as_str() {
                        "D" | "DIODE" => ModelKind::Diode,
                        "EKV_NMOS" | "NMOS" => ModelKind::EkvNmos,
                        "EKV_PMOS" | "PMOS" => ModelKind::EkvPmos,
                        "FINFET_N" | "BSIM_CMG_N" => ModelKind::FinFetN,
                        "FINFET_P" | "BSIM_CMG_P" => ModelKind::FinFetP,
                        "GAA_NMOS" | "NSFET_N" => ModelKind::GaaNmos,
                        "GAA_PMOS" | "NSFET_P" => ModelKind::GaaPmos,
                        "NPN" => ModelKind::Npn,
                        "PNP" => ModelKind::Pnp,
                        "SIGE_HBT" | "HBT_NPN" => ModelKind::SiGeHbt,
                        "GAN_HEMT" | "ASM_HEMT" => ModelKind::GanHemt,
                        "MLCC" => ModelKind::Mlcc,
                        other => return Err(err_ctx(format!("unknown model kind `{other}`"))),
                    };
                    let params = parse_kv_tokens(&toks[3..]).map_err(err_ctx)?;
                    deck.models
                        .insert(name.clone(), ModelDecl { name, kind, params });
                }
                ".pcb_microstrip" => {
                    if toks.len() < 6 {
                        return Err(err_ctx(
                            "expected `.pcb_microstrip <name> <in> <out> <ref> len=...`"
                                .to_string(),
                        ));
                    }
                    let kvs = parse_kv_tokens(&toks[5..]).map_err(err_ctx)?;
                    deck.elements.push(Element::PcbMicrostrip {
                        name: toks[1].clone(),
                        n_in: toks[2].clone(),
                        n_out: toks[3].clone(),
                        n_ref: toks[4].clone(),
                        len: get_req_expr(&kvs, "len", ".pcb_microstrip").map_err(err_ctx)?,
                        w0: get_req_expr(&kvs, "w0", ".pcb_microstrip").map_err(err_ctx)?,
                        dw: kvs.get("dw").cloned().unwrap_or_else(|| Expr::num(0.0)),
                        h0: get_req_expr(&kvs, "h0", ".pcb_microstrip").map_err(err_ctx)?,
                        dh: kvs.get("dh").cloned().unwrap_or_else(|| Expr::num(0.0)),
                        t_cu: get_req_expr(&kvs, "t_cu", ".pcb_microstrip").map_err(err_ctx)?,
                        er: get_req_expr(&kvs, "er", ".pcb_microstrip").map_err(err_ctx)?,
                        sigma_cu: kvs
                            .get("sigma_cu")
                            .cloned()
                            .unwrap_or_else(|| Expr::num(5.8e7)),
                    });
                }
                ".pcb_coupled_diffpair" => {
                    if toks.len() < 9 {
                        return Err(err_ctx(
                            "expected `.pcb_coupled_diffpair <name> <in_p> <in_n> <out_p> <out_n> <ref_in> <ref_out> ...`"
                                .to_string(),
                        ));
                    }
                    let kvs = parse_kv_tokens(&toks[8..]).map_err(err_ctx)?;
                    deck.elements.push(Element::PcbCoupledDiffpair {
                        name: toks[1].clone(),
                        in_p: toks[2].clone(),
                        in_n: toks[3].clone(),
                        out_p: toks[4].clone(),
                        out_n: toks[5].clone(),
                        ref_in: toks[6].clone(),
                        ref_out: toks[7].clone(),
                        len: get_req_expr(&kvs, "len", ".pcb_coupled_diffpair").map_err(err_ctx)?,
                        w0: get_req_expr(&kvs, "w0", ".pcb_coupled_diffpair").map_err(err_ctx)?,
                        dw: kvs.get("dw").cloned().unwrap_or_else(|| Expr::num(0.0)),
                        s0: get_req_expr(&kvs, "s0", ".pcb_coupled_diffpair").map_err(err_ctx)?,
                        ds: kvs.get("ds").cloned().unwrap_or_else(|| Expr::num(0.0)),
                        h0: get_req_expr(&kvs, "h0", ".pcb_coupled_diffpair").map_err(err_ctx)?,
                        dh: kvs.get("dh").cloned().unwrap_or_else(|| Expr::num(0.0)),
                        t_cu: get_req_expr(&kvs, "t_cu", ".pcb_coupled_diffpair")
                            .map_err(err_ctx)?,
                        er_p: get_req_expr(&kvs, "er_p", ".pcb_coupled_diffpair")
                            .map_err(err_ctx)?,
                        er_n: get_req_expr(&kvs, "er_n", ".pcb_coupled_diffpair")
                            .map_err(err_ctx)?,
                        l_via: kvs.get("l_via").cloned().unwrap_or_else(|| Expr::num(0.0)),
                        l_slot: kvs.get("l_slot").cloned().unwrap_or_else(|| Expr::num(0.0)),
                        r_ret: kvs
                            .get("r_ret")
                            .cloned()
                            .unwrap_or_else(|| Expr::num(0.005)),
                    });
                }
                ".tcad_finfet_2d" => {
                    if toks.len() < 3 {
                        return Err(err_ctx("expected `.tcad_finfet_2d <name> ...`".to_string()));
                    }
                    let kvs = parse_kv_tokens(&toks[2..]).map_err(err_ctx)?;
                    deck.elements.push(Element::TcadFinFet2D {
                        name: toks[1].clone(),
                        nx: get_req_f64(&kvs, "nx", ".tcad_finfet_2d").map_err(err_ctx)? as usize,
                        ny: get_req_f64(&kvs, "ny", ".tcad_finfet_2d").map_err(err_ctx)? as usize,
                        lg_nm: get_req_expr(&kvs, "lg_nm", ".tcad_finfet_2d").map_err(err_ctx)?,
                        tfin_nm: get_req_expr(&kvs, "tfin_nm", ".tcad_finfet_2d")
                            .map_err(err_ctx)?,
                        eot_nm: kvs
                            .get("eot_nm")
                            .cloned()
                            .unwrap_or_else(|| Expr::num(1.0)),
                        vgs: get_req_expr(&kvs, "vgs", ".tcad_finfet_2d").map_err(err_ctx)?,
                        vds: get_req_expr(&kvs, "vds", ".tcad_finfet_2d").map_err(err_ctx)?,
                        phim_shift: kvs
                            .get("phim_shift")
                            .cloned()
                            .unwrap_or_else(|| Expr::num(0.0)),
                        temp_k: kvs
                            .get("temp_k")
                            .cloned()
                            .unwrap_or_else(|| Expr::num(300.0)),
                        nbody_cm3: kvs
                            .get("nbody_cm3")
                            .cloned()
                            .unwrap_or_else(|| Expr::num(1.0e16)),
                    });
                }
                ".tcad_gaa_electrothermal" => {
                    if toks.len() < 3 {
                        return Err(err_ctx(
                            "expected `.tcad_gaa_electrothermal <name> ...`".to_string(),
                        ));
                    }
                    let kvs = parse_kv_tokens(&toks[2..]).map_err(err_ctx)?;
                    deck.elements.push(Element::TcadGaaElectroThermal {
                        name: toks[1].clone(),
                        nx: get_req_f64(&kvs, "nx", ".tcad_gaa_electrothermal").map_err(err_ctx)?
                            as usize,
                        nsheets: get_req_f64(&kvs, "nsheets", ".tcad_gaa_electrothermal")
                            .map_err(err_ctx)? as usize,
                        lg_nm: get_req_expr(&kvs, "lg_nm", ".tcad_gaa_electrothermal")
                            .map_err(err_ctx)?,
                        wns_nm: get_req_expr(&kvs, "wns_nm", ".tcad_gaa_electrothermal")
                            .map_err(err_ctx)?,
                        tns_nm: get_req_expr(&kvs, "tns_nm", ".tcad_gaa_electrothermal")
                            .map_err(err_ctx)?,
                        eot_nm: kvs
                            .get("eot_nm")
                            .cloned()
                            .unwrap_or_else(|| Expr::num(0.85)),
                        lisp_nm: kvs
                            .get("lisp_nm")
                            .cloned()
                            .unwrap_or_else(|| Expr::num(5.5)),
                        vgs: get_req_expr(&kvs, "vgs", ".tcad_gaa_electrothermal")
                            .map_err(err_ctx)?,
                        vds: get_req_expr(&kvs, "vds", ".tcad_gaa_electrothermal")
                            .map_err(err_ctx)?,
                        tamb_k: kvs
                            .get("tamb_k")
                            .cloned()
                            .unwrap_or_else(|| Expr::num(300.0)),
                        rth_kw: get_req_expr(&kvs, "rth_kw", ".tcad_gaa_electrothermal")
                            .map_err(err_ctx)?,
                    });
                }
                ".tcad_pn_1d" | ".tcad_diode_1d" => {
                    if toks.len() < 3 {
                        return Err(err_ctx("expected `.tcad_pn_1d <name> ...`".to_string()));
                    }
                    let kvs = parse_kv_tokens(&toks[2..]).map_err(err_ctx)?;
                    deck.elements.push(Element::TcadDiode1D {
                        name: toks[1].clone(),
                        nodes: get_req_f64(&kvs, "nodes", ".tcad_pn_1d").map_err(err_ctx)?
                            as usize,
                        length_um: get_req_f64(&kvs, "length_um", ".tcad_pn_1d")
                            .map_err(err_ctx)?,
                        junction_um: get_req_f64(&kvs, "junction_um", ".tcad_pn_1d")
                            .map_err(err_ctx)?,
                        q_dope: kvs
                            .get("q_dope")
                            .or_else(|| kvs.get("q_pwell"))
                            .cloned()
                            .ok_or_else(|| err_ctx("missing `q_dope` in `.tcad_pn_1d`".into()))?,
                        nd_plus: kvs
                            .get("nd_plus")
                            .cloned()
                            .unwrap_or_else(|| Expr::num(100.0)),
                        temp: kvs
                            .get("temp")
                            .cloned()
                            .unwrap_or_else(|| Expr::num(300.0)),
                        v_bias: get_req_expr(&kvs, "v_bias", ".tcad_pn_1d").map_err(err_ctx)?,
                    });
                }
                _ => return Err(err_ctx(format!("unknown directive `{head}`"))),
            }
            continue;
        }

        let first_char = head.chars().next().unwrap().to_ascii_uppercase();
        if head_lower.starts_with("c_mlcc") {
            if toks.len() < 4 {
                return Err(err_ctx(
                    "expected `C_MLCC<name> <n+> <n-> [model] params...`".to_string(),
                ));
            }
            let (model, kv_slice) = if toks[3].contains('=') {
                (None, &toks[3..])
            } else {
                (Some(toks[3].clone()), &toks[4..])
            };
            let kvs = parse_kv_tokens(kv_slice).map_err(err_ctx)?;
            let mod_params = model.as_ref().and_then(|m| deck.models.get(m));
            let lookup = |key: &str, default: f64| -> Expr {
                kvs.get(key)
                    .cloned()
                    .or_else(|| mod_params.and_then(|mp| mp.params.get(key).cloned()))
                    .unwrap_or_else(|| Expr::num(default))
            };
            deck.elements.push(Element::MlccCap {
                name: head.to_string(),
                n_pos: toks[1].clone(),
                n_neg: toks[2].clone(),
                model,
                c0: lookup("c0", 1e-6),
                c_min: lookup("cmin", 0.0),
                vsat: lookup("vsat", 1.0),
                esr: lookup("esr", 0.0),
                esl: lookup("esl", 0.0),
            });
            continue;
        }

        match first_char {
            'R' => {
                if toks.len() != 4 {
                    return Err(err_ctx("expected `R<name> <n+> <n-> <val>`".to_string()));
                }
                deck.elements.push(Element::Resistor {
                    name: head.to_string(),
                    n_pos: toks[1].clone(),
                    n_neg: toks[2].clone(),
                    r: parse_expr_str(&toks[3]).map_err(err_ctx)?,
                });
            }
            'C' => {
                if toks.len() != 4 {
                    return Err(err_ctx("expected `C<name> <n+> <n-> <val>`".to_string()));
                }
                deck.elements.push(Element::Capacitor {
                    name: head.to_string(),
                    n_pos: toks[1].clone(),
                    n_neg: toks[2].clone(),
                    c: parse_expr_str(&toks[3]).map_err(err_ctx)?,
                });
            }
            'L' => {
                if toks.len() < 4 {
                    return Err(err_ctx(
                        "expected `L<name> <n+> <n-> <val> [Rser=...]`".to_string(),
                    ));
                }
                let kvs = parse_kv_tokens(&toks[4..]).map_err(err_ctx)?;
                deck.elements.push(Element::Inductor {
                    name: head.to_string(),
                    n_pos: toks[1].clone(),
                    n_neg: toks[2].clone(),
                    l: parse_expr_str(&toks[3]).map_err(err_ctx)?,
                    r_ser: kvs.get("rser").cloned().unwrap_or_else(|| Expr::num(0.0)),
                });
            }
            'K' => {
                if toks.len() != 4 {
                    return Err(err_ctx("expected `K<name> <L1> <L2> <k>`".to_string()));
                }
                deck.elements.push(Element::CoupledInductors {
                    name: head.to_string(),
                    l1_name: toks[1].clone(),
                    l2_name: toks[2].clone(),
                    k: parse_expr_str(&toks[3]).map_err(err_ctx)?,
                });
            }
            'V' => {
                if toks.len() < 4 {
                    return Err(err_ctx(
                        "expected `V<name> <n+> <n-> <waveform>`".to_string(),
                    ));
                }
                deck.elements.push(Element::VoltageSource {
                    name: head.to_string(),
                    n_pos: toks[1].clone(),
                    n_neg: toks[2].clone(),
                    wave: parse_waveform(&toks[3..]).map_err(err_ctx)?,
                });
            }
            'I' => {
                if toks.len() < 4 {
                    return Err(err_ctx(
                        "expected `I<name> <n+> <n-> <waveform>`".to_string(),
                    ));
                }
                deck.elements.push(Element::CurrentSource {
                    name: head.to_string(),
                    n_pos: toks[1].clone(),
                    n_neg: toks[2].clone(),
                    wave: parse_waveform(&toks[3..]).map_err(err_ctx)?,
                });
            }
            'D' => {
                if toks.len() < 4 {
                    return Err(err_ctx(
                        "expected `D<name> <na> <nk> <model> [area=...]`".to_string(),
                    ));
                }
                let kvs = parse_kv_tokens(&toks[4..]).map_err(err_ctx)?;
                deck.elements.push(Element::Diode {
                    name: head.to_string(),
                    n_anode: toks[1].clone(),
                    n_cathode: toks[2].clone(),
                    model: toks[3].clone(),
                    area: kvs.get("area").cloned().unwrap_or_else(|| Expr::num(1.0)),
                    vt_override: kvs.get("vt").cloned(),
                });
            }
            'M' => {
                if toks.len() < 6 {
                    return Err(err_ctx(
                        "expected `M<name> <nd> <ng> <ns> <nb> <model> [params...]`".to_string(),
                    ));
                }
                let kvs = parse_kv_tokens(&toks[6..]).map_err(err_ctx)?;
                deck.elements.push(Element::Mosfet {
                    name: head.to_string(),
                    n_drain: toks[1].clone(),
                    n_gate: toks[2].clone(),
                    n_source: toks[3].clone(),
                    n_bulk: toks[4].clone(),
                    model: toks[5].clone(),
                    w: kvs.get("w").cloned().unwrap_or_else(|| Expr::num(1.0e-6)),
                    l: kvs.get("l").cloned().unwrap_or_else(|| Expr::num(1.0e-6)),
                    nfin: kvs
                        .get("nfin")
                        .or_else(|| kvs.get("nsheet"))
                        .cloned()
                        .unwrap_or_else(|| Expr::num(1.0)),
                    dtfin_nm: kvs
                        .get("dtfin")
                        .or_else(|| kvs.get("dtns"))
                        .cloned()
                        .unwrap_or_else(|| Expr::num(0.0)),
                    dvth: kvs.get("dvth").cloned().unwrap_or_else(|| Expr::num(0.0)),
                    dlisp_nm: kvs.get("dlisp").cloned().unwrap_or_else(|| Expr::num(0.0)),
                    rth: kvs.get("rth").cloned(),
                    vt_override: kvs.get("vt").cloned(),
                    tamb_k: kvs.get("tamb").cloned(),
                });
            }
            'Q' => {
                if toks.len() < 5 {
                    return Err(err_ctx(
                        "expected `Q<name> <nc> <nb> <ne> <model> [params...]`".to_string(),
                    ));
                }
                let kvs = parse_kv_tokens(&toks[5..]).map_err(err_ctx)?;
                deck.elements.push(Element::Bjt {
                    name: head.to_string(),
                    n_col: toks[1].clone(),
                    n_base: toks[2].clone(),
                    n_emit: toks[3].clone(),
                    model: toks[4].clone(),
                    area: kvs.get("area").cloned().unwrap_or_else(|| Expr::num(1.0)),
                    deg_ev: kvs.get("deg").cloned(),
                    vt_override: kvs.get("vt").cloned(),
                    temp_k: kvs.get("temp").cloned(),
                });
            }
            _ => {
                return Err(err_ctx(format!(
                    "unrecognized element or directive `{head}`"
                )));
            }
        }
    }

    Ok(deck)
}
