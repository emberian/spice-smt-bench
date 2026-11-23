use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process;

use spice2smt::ast::Dialect;
use spice2smt::pdk::PdkId;
use spice2smt::{compile_str_with_options, parser, paving, stamp};

fn print_usage() {
    eprintln!(
        "spice2smt 0.1.0 — SPICE / Multi-PDK / PCB / TCAD to Transcendental + ODE SMT-LIB2 & Lean 4

USAGE:
  spice2smt [compile] <deck.sp> [--dialect smt2-exp|dreal-ode|lean4] [--pdk <profile>] [--logic <QF_NRA|QF_NRAT|ALL>] [--name <Def>] [-o <out>]
  spice2smt batch <sp_dir> [--out-smt2-exp <dir>] [--out-dreal-ode <dir>] [--out-lean <file.lean>] [--logic <LOGIC>]
  spice2smt emit-lean <deck.sp> [--name <Def>] [--pdk <profile>] [-o <out.lean>]
  spice2smt generate-paving <deck.sp> <variable=mid>... -o <certificate.json|certificate.lean>
  spice2smt emit-witness <deck.sp> <variable=num/den>... -o <witness.lean>
  spice2smt emit-witness <03b.sp> --sram-boxes <samples.txt> <failure-step> -o <witness.lean>
  spice2smt verify-paving <deck.sp> <paving.json> [-o <certificate.lean>]
  spice2smt list-pdks

PDK PROFILES:
  asap7       7nm Multi-Gate FinFET (SLVT/RVT/SRAM, quantum confinement + DIBL)
  gt2n        2nm Gate-All-Around Stacked Nanosheet (inner-spacer Cisp + electro-thermal Rth)
  ihp_sg13g2  130nm SiGe BiCMOS (heterojunction SiGe HBT + Kirk roll-off)
  gan_sic     Wide-bandgap GaN-on-SiC HEMT + depletion Miller Cgd(Vds)
  gf180mcu    180nm Open Planar Bulk CMOS (3.3V/5V I/O + ESD + SCR)
  sky130      130nm Open Planar Bulk CMOS baseline"
    );
}

fn parse_dialect(s: &str) -> Result<Dialect, String> {
    match s.to_ascii_lowercase().as_str() {
        "smt2-exp" | "smt2" => Ok(Dialect::Smt2Exp),
        "dreal-ode" | "dreal" => Ok(Dialect::DrealOde),
        "lean4" | "lean" => Ok(Dialect::Lean4),
        other => Err(format!(
            "unknown dialect `{other}` (expected `smt2-exp`, `dreal-ode`, or `lean4`)"
        )),
    }
}

fn run() -> Result<(), String> {
    let args: Vec<String> = env::args().skip(1).collect();
    if args.is_empty() || args.iter().any(|a| a == "-h" || a == "--help") {
        print_usage();
        return Ok(());
    }

    match args[0].as_str() {
        "list-pdks" => {
            for pdk in PdkId::all() {
                let prof = pdk.profile();
                println!(
                    "{:<12} Vdd={:.2}V  Lg={:>5.1}nm  Tbody={:>5.1}nm  EOT={:.2}nm  | {}",
                    pdk.canonical_name(),
                    prof.vdd_nom_v,
                    prof.lg_nom_nm,
                    prof.t_body_nom_nm,
                    prof.eot_nom_nm,
                    prof.summary
                );
            }
            Ok(())
        }
        "generate-paving" => {
            if args.len() < 4 || args[args.len() - 2] != "-o" {
                return Err("usage: spice2smt generate-paving <deck.sp> <variable=mid>... -o <certificate.json|certificate.lean>".to_string());
            }
            let source = fs::read_to_string(&args[1]).map_err(|e| e.to_string())?;
            let system = stamp::stamp_deck(&parser::parse_deck(&source)?)?;
            let mut splits = Vec::new();
            for hint in &args[2..args.len() - 2] {
                let (variable, midpoint) = hint.split_once('=').ok_or("expected variable=midpoint")?;
                splits.push((variable.to_string(), parser::parse_spice_number(midpoint)?));
            }
            let certificate = paving::generate_paving(&system, &splits)?;
            let path = &args[args.len()-1];
            let output = if path.ends_with(".lean") { paving::lean::emit_paving(&system, &certificate)? }
                else { format!("{}\n", certificate.to_json()) };
            fs::write(path, output).map_err(|e| e.to_string())?;
            Ok(())
        }
        "emit-witness" => {
            if args.len() < 4 || args[args.len()-2] != "-o" {
                return Err("usage: emit-witness <deck.sp> <variable=num/den>... -o <witness.lean>".into());
            }
            let source = fs::read_to_string(&args[1]).map_err(|e| e.to_string())?;
            let sys = stamp::stamp_deck(&parser::parse_deck(&source)?)?;
            if args.get(2).map(String::as_str) == Some("--sram-boxes") {
                if args.len() != 7 {
                    return Err("expected --sram-boxes <samples.txt> <failure-step> -o <witness.lean>".into());
                }
                let rows = fs::read_to_string(&args[3]).map_err(|e| e.to_string())?;
                let failure = args[4].parse().map_err(|_| "expected integer failure step")?;
                let certificate = paving::lean::emit_sram_boxes(&sys, &rows, failure)?;
                return fs::write(&args[6], certificate).map_err(|e| e.to_string());
            }
            let mut values = std::collections::BTreeMap::new();
            for binding in &args[2..args.len()-2] {
                let (name, value) = binding.split_once('=').ok_or("expected variable=value")?;
                if values.insert(name.to_owned(),value.to_owned()).is_some() {
                    return Err(format!("duplicate witness for {name}"));
                }
            }
            fs::write(&args[args.len()-1], paving::lean::emit_witness(&sys, &values)?).map_err(|e| e.to_string())
        }
        "verify-paving" => {
            if args.len() != 3 && !(args.len() == 5 && args[3] == "-o") {
                return Err("usage: spice2smt verify-paving <deck.sp> <paving.json> [-o <certificate.lean>]".to_string());
            }
            let sp_src = fs::read_to_string(&args[1])
                .map_err(|e| format!("failed to read `{}`: {e}", args[1]))?;
            let json_src = fs::read_to_string(&args[2])
                .map_err(|e| format!("failed to read `{}`: {e}", args[2]))?;
            let deck = parser::parse_deck(&sp_src)?;
            let sys = stamp::stamp_deck(&deck)?;
            let pav = paving::parse_paving_json(&json_src)?;
            if args.len() == 5 {
                let text = paving::lean::emit_paving(&sys, &pav)?;
                return fs::write(&args[4], text).map_err(|e| e.to_string());
            }
            let rep = paving::verify_paving(&sys, &pav)?;
            println!(
                "VERIFIED UNSAT PAVING: total_leaves={} (unsafe_refuted={}, physics_refuted={}, max_depth={})",
                rep.total_leaves,
                rep.unsafe_refuted_leaves,
                rep.physics_refuted_leaves,
                rep.max_depth
            );
            Ok(())
        }
        "batch" => {
            if args.len() < 2 {
                return Err(
                    "usage: spice2smt batch <sp_dir> --out-smt2-exp <dir> --out-dreal-ode <dir>"
                        .to_string(),
                );
            }
            let sp_dir = PathBuf::from(&args[1]);
            let mut out_exp: Option<PathBuf> = None;
            let mut out_dreal: Option<PathBuf> = None;
            let mut out_lean: Option<PathBuf> = None;
            let mut logic_override: Option<String> = None;
            let mut i = 2;
            while i < args.len() {
                match args[i].as_str() {
                    "--out-smt2-exp" => {
                        i += 1;
                        out_exp = Some(PathBuf::from(
                            args.get(i).ok_or("missing path after --out-smt2-exp")?,
                        ));
                    }
                    "--out-dreal-ode" => {
                        i += 1;
                        out_dreal = Some(PathBuf::from(
                            args.get(i).ok_or("missing path after --out-dreal-ode")?,
                        ));
                    }
                    "--out-lean" => {
                        i += 1;
                        out_lean = Some(PathBuf::from(
                            args.get(i).ok_or("missing path after --out-lean")?,
                        ));
                    }
                    "--logic" => {
                        i += 1;
                        logic_override = Some(
                            args.get(i)
                                .ok_or("missing value after --logic")?
                                .to_string(),
                        );
                    }
                    other => return Err(format!("unknown batch flag `{other}`")),
                }
                i += 1;
            }
            if out_exp.is_none() && out_dreal.is_none() && out_lean.is_none() {
                return Err("batch requires at least one output flag".to_string());
            }
            if let Some(ref d) = out_exp {
                fs::create_dir_all(d).map_err(|e| format!("mkdir {}: {e}", d.display()))?;
            }
            if let Some(ref d) = out_dreal {
                fs::create_dir_all(d).map_err(|e| format!("mkdir {}: {e}", d.display()))?;
            }

            let mut entries: Vec<PathBuf> = fs::read_dir(&sp_dir)
                .map_err(|e| format!("failed to read dir {}: {e}", sp_dir.display()))?
                .filter_map(|r| r.ok().map(|e| e.path()))
                .filter(|p| p.extension().is_some_and(|ext| ext == "sp"))
                .collect();
            entries.sort();

            let mut lean_bundle = String::from(
                "import SpiceSmtBench.PhysicsModels\n\n/-!\n  Auto-generated by `spice2smt batch --out-lean` from `benchmarks/sp/*.sp`.\n  Every benchmark `Prop` below is stamped identically to `benchmarks/smt2/`.\n-/\n\nnamespace SpiceSmtBench.Targets\n\n",
            );

            for path in &entries {
                let stem = path
                    .file_stem()
                    .and_then(|s| s.to_str())
                    .ok_or("invalid file stem")?;
                let src = fs::read_to_string(path)
                    .map_err(|e| format!("read {}: {e}", path.display()))?;
                if let Some(ref d) = out_exp {
                    let smt = compile_str_with_options(
                        &src,
                        Dialect::Smt2Exp,
                        None,
                        None,
                        logic_override.as_deref(),
                    )
                    .map_err(|e| format!("{}: {e}", path.display()))?;
                    let dst = d.join(format!("{stem}.smt2"));
                    fs::write(&dst, smt).map_err(|e| format!("write {}: {e}", dst.display()))?;
                }
                if let Some(ref d) = out_dreal {
                    let smt = compile_str_with_options(
                        &src,
                        Dialect::DrealOde,
                        None,
                        None,
                        logic_override.as_deref(),
                    )
                    .map_err(|e| format!("{}: {e}", path.display()))?;
                    let dst = d.join(format!("{stem}.smt2"));
                    fs::write(&dst, smt).map_err(|e| format!("write {}: {e}", dst.display()))?;
                }
                if out_lean.is_some() {
                    let deck =
                        parser::parse_deck(&src).map_err(|e| format!("{}: {e}", path.display()))?;
                    let sys =
                        stamp::stamp_deck(&deck).map_err(|e| format!("{}: {e}", path.display()))?;
                    let def_name = format!("Bench_{stem}");
                    lean_bundle.push_str(&spice2smt::emit_lean::emit_lean_def(
                        &sys, &def_name, false,
                    ));
                    lean_bundle.push('\n');
                }
            }
            if let Some(ref dst) = out_lean {
                lean_bundle.push_str("end SpiceSmtBench.Targets\n");
                if let Some(parent) = dst.parent() {
                    if !parent.as_os_str().is_empty() {
                        fs::create_dir_all(parent)
                            .map_err(|e| format!("mkdir {}: {e}", parent.display()))?;
                    }
                }
                fs::write(dst, lean_bundle)
                    .map_err(|e| format!("write {}: {e}", dst.display()))?;
            }
            println!("Compiled {} benchmark decks from {}", entries.len(), sp_dir.display());
            Ok(())
        }
        _ => {
            let lean_alias = args[0] == "emit-lean";
            let start = if args[0] == "compile" || lean_alias { 1 } else { 0 };
            let sp_path = args
                .get(start)
                .ok_or("missing input `<deck.sp>` path")?;
            let mut dialect = if lean_alias { Dialect::Lean4 } else { Dialect::Smt2Exp };
            let mut pdk_override: Option<PdkId> = None;
            let mut def_name: Option<String> = None;
            let mut logic_override: Option<String> = None;
            let mut out_path: Option<PathBuf> = None;

            let mut i = start + 1;
            while i < args.len() {
                match args[i].as_str() {
                    "--dialect" | "-d" => {
                        i += 1;
                        let val = args.get(i).ok_or("missing value after --dialect")?;
                        dialect = parse_dialect(val)?;
                    }
                    "--pdk" => {
                        i += 1;
                        let val = args.get(i).ok_or("missing value after --pdk")?;
                        pdk_override = Some(
                            PdkId::parse(val).ok_or_else(|| format!("unknown PDK `{val}`"))?,
                        );
                    }
                    "--logic" => {
                        i += 1;
                        logic_override = Some(
                            args.get(i)
                                .ok_or("missing value after --logic")?
                                .to_string(),
                        );
                    }
                    "--name" => {
                        i += 1;
                        def_name = Some(
                            args.get(i)
                                .ok_or("missing value after --name")?
                                .to_string(),
                        );
                    }
                    "-o" | "--output" => {
                        i += 1;
                        out_path = Some(PathBuf::from(
                            args.get(i).ok_or("missing path after -o")?,
                        ));
                    }
                    other => return Err(format!("unknown flag `{other}`")),
                }
                i += 1;
            }

            if dialect != Dialect::Lean4 && def_name.is_some() {
                return Err("--name is only supported for Lean output".to_string());
            }
            let src = fs::read_to_string(sp_path)
                .map_err(|e| format!("failed to read `{sp_path}`: {e}"))?;
            let default_stem = Path::new(sp_path)
                .file_stem()
                .and_then(|s| s.to_str())
                .unwrap_or("CircuitTargetSpec");
            let rendered = compile_str_with_options(
                &src,
                dialect,
                pdk_override,
                if dialect == Dialect::Lean4 { Some(def_name.as_deref().unwrap_or(default_stem)) } else { None },
                logic_override.as_deref(),
            )?;
            if let Some(dst) = out_path {
                if let Some(parent) = dst.parent() {
                    if !parent.as_os_str().is_empty() {
                        fs::create_dir_all(parent)
                            .map_err(|e| format!("mkdir {}: {e}", parent.display()))?;
                    }
                }
                fs::write(&dst, rendered)
                    .map_err(|e| format!("failed to write `{}`: {e}", dst.display()))?;
            } else {
                print!("{rendered}");
            }
            Ok(())
        }
    }
}

fn main() {
    if let Err(err) = run() {
        eprintln!("error: {err}");
        process::exit(1);
    }
}
