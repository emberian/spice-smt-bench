//! `spice2smt`: Zero-dependency SPICE netlist, Multi-PDK transistor (`asap7` FinFET,
//! `gt2n` 2nm GAA nanosheet, `ihp_sg13g2` SiGe HBT, `gan_sic` HEMT, `gf180mcu`/`sky130`),
//! continuous-defect PCB multiphysics, and 2D/electro-thermal TCAD compiler to
//! Transcendental + ODE SMT-LIB2 (`ALL` / `QF_NRA_ODE`) and Lean 4 target specifications.

pub mod ast;
pub mod emit_lean;
pub mod emit_smt2;
pub mod numeral;
pub mod parser;
pub mod paving;
pub mod pdk;
pub mod stamp;

use crate::ast::Dialect;
use crate::pdk::PdkId;

/// Compile a `.sp` deck source string directly to the requested target dialect.
pub fn compile_str(
    source: &str,
    dialect: Dialect,
    pdk_override: Option<PdkId>,
    lean_def_name: Option<&str>,
) -> Result<String, String> {
    compile_str_with_options(source, dialect, pdk_override, lean_def_name, None)
}

/// Compile a `.sp` deck source string with an optional SMT-LIB2 `(set-logic ...)` override.
pub fn compile_str_with_options(
    source: &str,
    dialect: Dialect,
    pdk_override: Option<PdkId>,
    lean_def_name: Option<&str>,
    smt_logic_override: Option<&str>,
) -> Result<String, String> {
    if dialect == Dialect::Lean4 && smt_logic_override.is_some() {
        return Err("--logic is only supported for SMT dialects".to_string());
    }
    if dialect != Dialect::Lean4 && lean_def_name.is_some() {
        return Err("--name is only supported for Lean output".to_string());
    }
    let overridden;
    let source = if let Some(pdk) = pdk_override {
        let lines = source
            .lines()
            .filter(|line| {
                !line
                    .split_whitespace()
                    .next()
                    .is_some_and(|head| head.eq_ignore_ascii_case(".pdk"))
            })
            .collect::<Vec<_>>()
            .join("\n");
        overridden = format!(".pdk {}\n{lines}", pdk.canonical_name());
        &overridden
    } else {
        source
    };
    let deck = parser::parse_deck(source)?;
    let sys = stamp::stamp_deck(&deck)?;
    match dialect {
        Dialect::Smt2Exp | Dialect::DrealOde => {
            emit_smt2::emit_smt2_with_logic(&sys, dialect, smt_logic_override)
        }
        Dialect::Lean4 => Ok(emit_lean::emit_lean_def(
            &sys,
            lean_def_name.unwrap_or("CircuitTargetSpec"),
            true,
        )),
    }
}
