//! `spice2smt`: Zero-dependency SPICE netlist, Multi-PDK transistor (`asap7` FinFET,
//! `gt2n` 2nm GAA nanosheet, `ihp_sg13g2` SiGe HBT, `gan_sic` HEMT, `gf180mcu`/`sky130`),
//! continuous-defect PCB multiphysics, and 2D/electro-thermal TCAD compiler to
//! Transcendental + ODE SMT-LIB2 (`QF_NRA + exp + ODE`) and Lean 4 target specifications.

pub mod ast;
pub mod emit_lean;
pub mod emit_smt2;
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
    let mut deck = parser::parse_deck(source)?;
    if let Some(pdk) = pdk_override {
        parser::apply_pdk_defaults(&mut deck, pdk);
    }
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
