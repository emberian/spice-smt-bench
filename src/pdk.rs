//! Built-in Multi-PDK Process Design Kit registry spanning 7nm FinFET (`asap7`),
//! 2nm Gate-All-Around stacked nanosheets (`gt2n`), 130nm SiGe BiCMOS (`ihp_sg13g2`),
//! wide-bandgap GaN-on-SiC power/RF HEMTs (`gan_sic`), and open planar bulk CMOS
//! baselines (`gf180mcu`, `sky130`).

use std::collections::BTreeMap;
use std::fmt;

use crate::ast::{Expr, ModelDecl, ModelKind};

/// Supported open and predictive technology PDK profiles.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum PdkId {
    /// 7nm Predictive Multi-Gate FinFET PDK (Clark et al., ASU/Arm `ASAP7` class:
    /// `SLVT` / `LVT` / `RVT` / `SRAM`, `Lg = 21nm`, `Tfin = 6.5nm`, `Hfin = 32nm`, `EOT = 1.0nm`).
    Asap7,
    /// 2nm Gate-All-Around Stacked Nanosheet / RibbonFET Predictive PDK (`gt2n` / `gaa2n`:
    /// 3-sheet GAA stack, `Lg = 12nm`, `Wns = 18nm`, `Tns = 5.0nm`, `EOT = 0.85nm`, coupled self-heating).
    Gt2n,
    /// Open 130nm SiGe BiCMOS (`IHP SG13G2` class: 350/450 GHz heterojunction SiGe HBT + CMOS).
    IhpSg13g2,
    /// Wide-bandgap AlGaN/GaN-on-SiC HEMT & 4H-SiC power/RF technology (`ASM-HEMT` class).
    GanSic,
    /// Open 180nm planar bulk MCU/analog CMOS (`GF180MCU` class, 3.3V/5V + 1.8V).
    Gf180Mcu,
    /// Open 130nm planar bulk CMOS (`SKY130` class, baseline planar reference).
    Sky130,
}

impl PdkId {
    pub fn parse(raw: &str) -> Option<Self> {
        match raw.trim().to_ascii_lowercase().as_str() {
            "asap7" | "finfet7" | "7nm" => Some(PdkId::Asap7),
            "gt2n" | "gaa2n" | "2nm" | "nanosheet2n" => Some(PdkId::Gt2n),
            "ihp_sg13g2" | "sg13g2" | "ihp130" | "sige130" => Some(PdkId::IhpSg13g2),
            "gan_sic" | "gansic" | "gan_hemt" | "asm_hemt" => Some(PdkId::GanSic),
            "gf180mcu" | "gf180" => Some(PdkId::Gf180Mcu),
            "sky130" | "sky130a" => Some(PdkId::Sky130),
            _ => None,
        }
    }

    pub fn canonical_name(self) -> &'static str {
        match self {
            PdkId::Asap7 => "asap7",
            PdkId::Gt2n => "gt2n",
            PdkId::IhpSg13g2 => "ihp_sg13g2",
            PdkId::GanSic => "gan_sic",
            PdkId::Gf180Mcu => "gf180mcu",
            PdkId::Sky130 => "sky130",
        }
    }

    pub fn all() -> &'static [PdkId] {
        &[
            PdkId::Asap7,
            PdkId::Gt2n,
            PdkId::IhpSg13g2,
            PdkId::GanSic,
            PdkId::Gf180Mcu,
            PdkId::Sky130,
        ]
    }
}

impl fmt::Display for PdkId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.canonical_name())
    }
}

/// Physical technology summary for a PDK profile.
#[derive(Debug, Clone)]
pub struct PdkProfile {
    pub id: PdkId,
    pub summary: &'static str,
    pub vdd_nom_v: f64,
    pub lg_nom_nm: f64,
    pub t_body_nom_nm: f64,
    pub eot_nom_nm: f64,
    pub default_models: Vec<ModelDecl>,
}

fn model_card(name: &str, kind: ModelKind, kvs: &[(&str, f64)]) -> ModelDecl {
    let mut params = BTreeMap::new();
    for (k, v) in kvs {
        params.insert((*k).to_ascii_lowercase(), Expr::num(*v));
    }
    ModelDecl {
        name: name.to_string(),
        kind,
        params,
    }
}

impl PdkId {
    /// Retrieve the physically grounded parameter profile and default `.model` deck for this PDK.
    pub fn profile(self) -> PdkProfile {
        match self {
            PdkId::Asap7 => PdkProfile {
                id: PdkId::Asap7,
                summary: "7nm Multi-Gate FinFET (Clark et al. ASAP7 class: Lg=21nm, Tfin=6.5nm, Hfin=32nm, HfO2 EOT=1.0nm, quantum confinement + DIBL)",
                vdd_nom_v: 0.70,
                lg_nom_nm: 21.0,
                t_body_nom_nm: 6.5,
                eot_nom_nm: 1.0,
                default_models: vec![
                    model_card(
                        "ASAP7_NFET_RVT",
                        ModelKind::FinFetN,
                        &[
                            ("is0", 1.8e-6),
                            ("vt0", 0.27),
                            ("kappa", 0.86),
                            ("lg_nm", 21.0),
                            ("tfin_nm", 6.5),
                            ("hfin_nm", 32.0),
                            ("eot_nm", 1.0),
                            ("alpha_qm", 1.71),
                            ("eta_dibl0", 3.2),
                        ],
                    ),
                    model_card(
                        "ASAP7_PFET_RVT",
                        ModelKind::FinFetP,
                        &[
                            ("is0", 1.45e-6),
                            ("vt0", 0.28),
                            ("kappa", 0.85),
                            ("lg_nm", 21.0),
                            ("tfin_nm", 6.5),
                            ("hfin_nm", 32.0),
                            ("eot_nm", 1.0),
                            ("alpha_qm", 1.71),
                            ("eta_dibl0", 3.4),
                        ],
                    ),
                    model_card(
                        "ASAP7_NFET_SLVT",
                        ModelKind::FinFetN,
                        &[
                            ("is0", 2.2e-6),
                            ("vt0", 0.19),
                            ("kappa", 0.88),
                            ("lg_nm", 21.0),
                            ("tfin_nm", 6.5),
                            ("hfin_nm", 32.0),
                            ("eot_nm", 1.0),
                            ("alpha_qm", 1.71),
                            ("eta_dibl0", 3.2),
                        ],
                    ),
                    model_card(
                        "ASAP7_PFET_SLVT",
                        ModelKind::FinFetP,
                        &[
                            ("is0", 1.85e-6),
                            ("vt0", 0.20),
                            ("kappa", 0.87),
                            ("lg_nm", 21.0),
                            ("tfin_nm", 6.5),
                            ("hfin_nm", 32.0),
                            ("eot_nm", 1.0),
                            ("alpha_qm", 1.71),
                            ("eta_dibl0", 3.4),
                        ],
                    ),
                    model_card(
                        "ASAP7_NFET_SRAM",
                        ModelKind::FinFetN,
                        &[
                            ("is0", 1.55e-6),
                            ("vt0", 0.32),
                            ("kappa", 0.85),
                            ("lg_nm", 21.0),
                            ("tfin_nm", 6.5),
                            ("hfin_nm", 32.0),
                            ("eot_nm", 1.0),
                            ("alpha_qm", 1.71),
                            ("eta_dibl0", 3.0),
                        ],
                    ),
                    model_card(
                        "ASAP7_PFET_SRAM",
                        ModelKind::FinFetP,
                        &[
                            ("is0", 1.25e-6),
                            ("vt0", 0.33),
                            ("kappa", 0.84),
                            ("lg_nm", 21.0),
                            ("tfin_nm", 6.5),
                            ("hfin_nm", 32.0),
                            ("eot_nm", 1.0),
                            ("alpha_qm", 1.71),
                            ("eta_dibl0", 3.2),
                        ],
                    ),
                ],
            },
            PdkId::Gt2n => PdkProfile {
                id: PdkId::Gt2n,
                summary: "2nm Gate-All-Around Stacked Nanosheet (gt2n: Nsheet=3, Lg=12nm, Wns=18nm, Tns=5.0nm, EOT=0.85nm, inner-spacer Cisp + electro-thermal Rth)",
                vdd_nom_v: 0.65,
                lg_nom_nm: 12.0,
                t_body_nom_nm: 5.0,
                eot_nom_nm: 0.85,
                default_models: vec![
                    model_card(
                        "GT2N_NFET_GAA",
                        ModelKind::GaaNmos,
                        &[
                            ("is0", 2.6e-6),
                            ("vt0", 0.23),
                            ("kappa", 0.91),
                            ("lg_nm", 12.0),
                            ("wns_nm", 18.0),
                            ("tns_nm", 5.0),
                            ("nsheet", 3.0),
                            ("eot_nm", 0.85),
                            ("lisp_nm", 5.5),
                            ("alpha_qm", 1.71),
                            ("eta_dibl0", 2.8),
                            ("kt_vth", 0.00085),
                        ],
                    ),
                    model_card(
                        "GT2N_PFET_GAA",
                        ModelKind::GaaPmos,
                        &[
                            ("is0", 2.25e-6),
                            ("vt0", 0.24),
                            ("kappa", 0.90),
                            ("lg_nm", 12.0),
                            ("wns_nm", 18.0),
                            ("tns_nm", 5.0),
                            ("nsheet", 3.0),
                            ("eot_nm", 0.85),
                            ("lisp_nm", 5.5),
                            ("alpha_qm", 1.71),
                            ("eta_dibl0", 2.9),
                            ("kt_vth", 0.00085),
                        ],
                    ),
                ],
            },
            PdkId::IhpSg13g2 => PdkProfile {
                id: PdkId::IhpSg13g2,
                summary: "Open 130nm SiGe BiCMOS (IHP SG13G2 class: heterojunction SiGe HBT with Ge bandgap narrowing + Kirk high-injection roll-off)",
                vdd_nom_v: 1.20,
                lg_nom_nm: 130.0,
                t_body_nom_nm: 40.0,
                eot_nom_nm: 2.6,
                default_models: vec![
                    model_card(
                        "SG13_NPN_HBT",
                        ModelKind::SiGeHbt,
                        &[
                            ("is", 3.2e-18),
                            ("bf", 380.0),
                            ("br", 8.0),
                            ("deg_ev", 0.085),
                            ("ikirk", 0.012),
                        ],
                    ),
                    model_card(
                        "SG13_NMOS",
                        ModelKind::EkvNmos,
                        &[("is0", 8.5e-7), ("vt0", 0.41), ("kappa", 0.76)],
                    ),
                    model_card(
                        "SG13_PMOS",
                        ModelKind::EkvPmos,
                        &[("is0", 3.4e-7), ("vt0", 0.43), ("kappa", 0.74)],
                    ),
                ],
            },
            PdkId::GanSic => PdkProfile {
                id: PdkId::GanSic,
                summary: "Wide-Bandgap AlGaN/GaN-on-SiC Power & RF HEMT (ASM-HEMT 2DEG polarization channel + voltage-dependent depletion Miller Cgd)",
                vdd_nom_v: 48.0,
                lg_nom_nm: 250.0,
                t_body_nom_nm: 22.0,
                eot_nom_nm: 3.5,
                default_models: vec![
                    model_card(
                        "GAN_EHEMT_100V",
                        ModelKind::GanHemt,
                        &[
                            ("is0", 0.018),
                            ("vt0", 1.45),
                            ("kappa", 0.82),
                            ("vtheta", 0.12),
                        ],
                    ),
                    model_card(
                        "GAN_CGD_MILLER",
                        ModelKind::Mlcc,
                        &[
                            ("c0", 42e-12),
                            ("cmin", 3.5e-12),
                            ("vsat", 8.0),
                            ("esr", 0.0),
                            ("esl", 0.0),
                        ],
                    ),
                    model_card("SIC_SBD", ModelKind::Diode, &[("is", 2.0e-13), ("n", 1.08)]),
                ],
            },
            PdkId::Gf180Mcu => PdkProfile {
                id: PdkId::Gf180Mcu,
                summary: "Open 180nm Planar Bulk CMOS (GF180MCU class: 3.3V/5V I/O + ESD diodes + parasitic well/substrate SCR)",
                vdd_nom_v: 3.30,
                lg_nom_nm: 180.0,
                t_body_nom_nm: 180.0,
                eot_nom_nm: 4.2,
                default_models: vec![
                    model_card("GF180_DIODE_ESD", ModelKind::Diode, &[("is", 1.0e-14), ("n", 1.05)]),
                    model_card(
                        "GF180_NMOS_3V3",
                        ModelKind::EkvNmos,
                        &[("is0", 6.2e-7), ("vt0", 0.56), ("kappa", 0.72)],
                    ),
                    model_card(
                        "GF180_PMOS_3V3",
                        ModelKind::EkvPmos,
                        &[("is0", 2.4e-7), ("vt0", 0.60), ("kappa", 0.70)],
                    ),
                    model_card("GF180_SCR_NPN", ModelKind::Npn, &[("is", 2.5e-16), ("bf", 45.0), ("br", 2.0)]),
                    model_card("GF180_SCR_PNP", ModelKind::Pnp, &[("is", 1.8e-16), ("bf", 18.0), ("br", 1.5)]),
                ],
            },
            PdkId::Sky130 => PdkProfile {
                id: PdkId::Sky130,
                summary: "Open 130nm Planar Bulk CMOS (SKY130 baseline planar reference)",
                vdd_nom_v: 1.80,
                lg_nom_nm: 150.0,
                t_body_nom_nm: 150.0,
                eot_nom_nm: 3.2,
                default_models: vec![
                    model_card("SKY130_DIODE", ModelKind::Diode, &[("is", 1.2e-14), ("n", 1.06)]),
                    model_card(
                        "SKY130_NMOS",
                        ModelKind::EkvNmos,
                        &[("is0", 7.8e-7), ("vt0", 0.46), ("kappa", 0.74)],
                    ),
                    model_card(
                        "SKY130_PMOS",
                        ModelKind::EkvPmos,
                        &[("is0", 3.1e-7), ("vt0", 0.49), ("kappa", 0.72)],
                    ),
                ],
            },
        }
    }
}
