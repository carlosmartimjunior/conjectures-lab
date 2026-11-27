pub mod ablation;
pub mod fixed_u128;
pub mod lean_cert_gen;
pub mod sat_m1;
pub mod sieve_cover;

use ablation::run_full_ablation;
use fixed_u128::{
    sieve_primes, test_interval_exact, PmTable, PrefixHarmonicBounds, PropagatorBuffers, ONE_SCALED,
};
use lean_cert_gen::generate_lean_certificate;
use sat_m1::{export_m1_dimacs_cnf, export_m1_smt2, solve_sat_m1};
use sieve_cover::verify_up_to_max_b;
use std::env;
use std::fs;
use std::path::PathBuf;

fn parse_u32_flag(args: &[String], flag: &str, default: u32) -> u32 {
    for i in 0..args.len().saturating_sub(1) {
        if args[i] == flag {
            if let Ok(v) = args[i + 1].parse::<u32>() {
                return v;
            }
        }
    }
    default
}

fn certs_dir() -> PathBuf {
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let dir = manifest_dir.parent().unwrap().join("certificates");
    let _ = fs::create_dir_all(&dir);
    dir
}

fn cmd_sanity() {
    println!("=== Running Sanity & Baseline Concordance Checks ===");
    let pm = PmTable::compute(18);
    println!("Computed exact P_m sets up to m = 18:");
    for entry in pm.summary().iter().filter(|e| [1, 2, 3, 4, 6, 10, 16, 18].contains(&e.m)) {
        println!(
            "  m={:2}: D_m={:<10} D_m*H_m={:<10} |P_m|={:<6} max(P_m)={}",
            entry.m, entry.d_m, entry.max_n_c, entry.num_primes, entry.max_prime
        );
    }

    let (_, primes) = sieve_primes(2000);
    let pref = PrefixHarmonicBounds::new(2000);
    let mut buf = PropagatorBuffers::with_capacity(2001);

    for &(name, a, b) in &[("[2,6]", 2u32, 6u32), ("[2,12]", 2, 12), ("[2,42]", 2, 42)] {
        let res = test_interval_exact(a, b, &primes, &mut buf, 12, false);
        assert!(!res.killed, "Sanity check failed on {name}!");
        assert!(res.min_sum_lo <= ONE_SCALED && res.max_sum_hi >= ONE_SCALED);
        println!("  PASS: {name} without gap<=2 survived as required.");
    }

    let mut total_cands = 0usize;
    let mut survivors = 0usize;
    for b in 4..=2000 {
        for a in pref.candidate_a_list(b) {
            total_cands += 1;
            let res = test_interval_exact(a, b, &primes, &mut buf, 10, true);
            if !res.killed {
                survivors += 1;
            }
        }
    }
    assert_eq!(total_cands, 464_286);
    assert_eq!(survivors, 0);
    println!("  PASS: b <= 2000 exact concordance: 464,286 candidates, 0 survivors (zero f64!).");
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let subcmd = args.get(1).map(|s| s.as_str()).unwrap_or("all");

    match subcmd {
        "sanity" => cmd_sanity(),
        "sat-m1" => {
            let b = parse_u32_flag(&args, "--b", 180);
            let max_p = parse_u32_flag(&args, "--max-p", 13);
            let pref = PrefixHarmonicBounds::new(b);
            let cands = pref.candidate_a_list(b);
            let a = cands[cands.len() / 2];
            let tol = ONE_SCALED / 100_000; // 10^-5
            let res = solve_sat_m1(a, b, max_p, true, tol, 200_000);
            println!("SAT-M1 on [{a}, {b}] (max_p={max_p}, tol=1e-5): {res:#?}");

            let dir = certs_dir();
            fs::write(
                dir.join(format!("m1_instance_{a}_{b}.smt2")),
                export_m1_smt2(a, b, max_p, 10),
            )
            .unwrap();
            fs::write(
                dir.join(format!("m1_instance_{a}_{b}.cnf")),
                export_m1_dimacs_cnf(a, b, max_p),
            )
            .unwrap();
            println!("Exported SMT-LIB2 and DIMACS CNF instances to {}", dir.display());
        }
        "ablation" => {
            let max_b = parse_u32_flag(&args, "--max-b", 6000);
            let max_b_m3 = parse_u32_flag(&args, "--max-b-m3", 10_000_000);
            let report = run_full_ablation(max_b, max_b_m3);
            let out_path = certs_dir().join("ablation_report.json");
            fs::write(&out_path, serde_json::to_string_pretty(&report).unwrap()).unwrap();
            println!("Ablation completed in {:.2}s -> {}", report.elapsed_secs, out_path.display());
            println!("  M1 (p<=13 prop, b<={max_b}): killed {}/{} (survivors: {})",
                report.m1_prop_small_primes_p13.killed_count,
                report.m1_prop_small_primes_p13.total_candidates,
                report.m1_prop_small_primes_p13.survivor_count);
            println!("  M2 (p^r>b/2 only, b<={max_b}): killed {}/{} (survivors: {})",
                report.m2_half_primes_only.killed_count,
                report.m2_half_primes_only.total_candidates,
                report.m2_half_primes_only.survivor_count);
            println!("  M4 (Full exact u128, b<={max_b}): killed {}/{} (survivors: {})",
                report.m4_full_propagation.killed_count,
                report.m4_full_propagation.total_candidates,
                report.m4_full_propagation.survivor_count);
            println!("  M3 (NO Sophie Germain, b<={max_b_m3}): contiguous cover from b = {} (uncovered count: {})",
                report.m3_no_sophie_germain_cover_10m.contiguous_universal_cover_from_b,
                report.m3_no_sophie_germain_cover_10m.uncovered_b_count);
            println!("  SAT-M1 exact carry probe (p<=13, tol=1e-5): tested={}, UNSAT={}, SAT pseudo-solutions={}",
                report.sat_m1_exact_carry_probe.tested_intervals,
                report.sat_m1_exact_carry_probe.unsat_count,
                report.sat_m1_exact_carry_probe.sat_pseudo_solution_count);
        }
        "verify-100m" => {
            let max_b = parse_u32_flag(&args, "--max-b", 100_000_000);
            let summary = verify_up_to_max_b(max_b, 18);
            let out_path = certs_dir().join("verify_100m_summary.json");
            fs::write(&out_path, serde_json::to_string_pretty(&summary).unwrap()).unwrap();
            println!(
                "Verified ALL 4 <= b <= {} in {:.2}s -> {}!",
                summary.max_b,
                summary.elapsed_secs,
                out_path.display()
            );
            println!(
                "  Greedy universal 64-block witnesses: {} (covered {} values of b)",
                summary.greedy_cover_witness_count, summary.universal_covered_b_count
            );
            println!(
                "  Fallback b values: {:?} ({} candidate intervals, survivors = {})",
                summary.fallback_b_values,
                summary.fallback_candidate_intervals_tested,
                summary.total_survivors
            );
            assert_eq!(summary.total_survivors, 0);
        }
        "export-lean-cert" => {
            let max_b_lean = parse_u32_flag(&args, "--max-b", 20_000);
            let max_m_lean = parse_u32_flag(&args, "--max-m", 6) as usize;
            let bundle = generate_lean_certificate(max_b_lean, max_m_lean);
            let out_path = certs_dir().join("lean_witnesses_20k.json");
            fs::write(&out_path, serde_json::to_string_pretty(&bundle).unwrap()).unwrap();
            println!(
                "Generated Lean 4 certificate up to b = {}: {} universal 4-block witnesses, {} small b values ({} small intervals) -> {}",
                bundle.max_b_lean,
                bundle.universal_4block_witnesses.len(),
                bundle.uncovered_small_bs.len(),
                bundle.uncovered_candidate_pairs.len(),
                out_path.display()
            );
        }
        "all" => {
            cmd_sanity();
            let bundle = generate_lean_certificate(20_000, 6);
            fs::write(
                certs_dir().join("lean_witnesses_20k.json"),
                serde_json::to_string_pretty(&bundle).unwrap(),
            )
            .unwrap();
            println!(
                "Lean 20k certificate: {} universal 4-block witnesses, {} small b values ({:?}), {} small candidate intervals.",
                bundle.universal_4block_witnesses.len(),
                bundle.uncovered_small_bs.len(),
                bundle.uncovered_small_bs,
                bundle.uncovered_candidate_pairs.len()
            );
            let report = run_full_ablation(6000, 10_000_000);
            fs::write(
                certs_dir().join("ablation_report.json"),
                serde_json::to_string_pretty(&report).unwrap(),
            )
            .unwrap();
            println!(
                "Ablation summary: M1 survivors={}, M2 survivors={}, M4 survivors={}, SAT-M1 pseudo-solutions={}, M3 (no SG <=10M) contiguous from b={}",
                report.m1_prop_small_primes_p13.survivor_count,
                report.m2_half_primes_only.survivor_count,
                report.m4_full_propagation.survivor_count,
                report.sat_m1_exact_carry_probe.sat_pseudo_solution_count,
                report.m3_no_sophie_germain_cover_10m.contiguous_universal_cover_from_b
            );
            let summary = verify_up_to_max_b(100_000_000, 18);
            fs::write(
                certs_dir().join("verify_100m_summary.json"),
                serde_json::to_string_pretty(&summary).unwrap(),
            )
            .unwrap();
            println!(
                "10^8 verification: {} universal witnesses + {} fallback b values -> {} survivors in {:.2}s!",
                summary.greedy_cover_witness_count,
                summary.fallback_b_values.len(),
                summary.total_survivors,
                summary.elapsed_secs
            );
        }
        other => {
            eprintln!("Unknown subcommand: {other}");
            std::process::exit(1);
        }
    }
}
