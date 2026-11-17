//! Opt-in origin-attempt audit of a real chip; does not require a Lean proof replay.

use std::{collections::BTreeMap, sync::Mutex};

use p3_air::BaseAir;
use zkm_core_machine::MipsAir;
use zkm_pcs::MachineAir;
use zkm_picus::{
    pcl::{initialize_fresh_var_ctr, set_field_modulus, Felt, PicusExpr},
    picus_builder::{
        build_selector_env, extract_module, ColumnOutputMode, ExtractionConfig,
        PortOriginAttempt, ShrCarrySummaryMode, SubmoduleMode, PORT_ORIGIN_ATTEMPTS,
        PORT_ORIGIN_AUDIT_ENABLED,
    },
};

// Both native tests change the process-global opt-in flag, so they must not overlap.
static AUDIT_TEST_GUARD: Mutex<()> = Mutex::new(());

fn config() -> ExtractionConfig {
    ExtractionConfig {
        submodule_mode: SubmoduleMode::Inline,
        shr_carry: ShrCarrySummaryMode::AbstractModule,
        column_output_mode: ColumnOutputMode::InteractionsOnly,
        reify_threshold: 128,
    }
}

#[test]
fn syslinux_audit_records_lost_roles_without_changing_ports() {
    let _guard = AUDIT_TEST_GUARD.lock().unwrap();
    let _ = set_field_modulus(0x7f00_0001);
    let chips = MipsAir::<Felt>::chips();
    let chip = chips.iter().find(|chip| chip.name() == "SysLinux").expect("SysLinux chip");
    let info = chip.picus_info();
    let env = build_selector_env(&info, None, true);
    let name = "SysLinux__mathgraph_origin_audit";
    let fresh_base = 10 * chip.air.width() + 1024;

    PORT_ORIGIN_AUDIT_ENABLED.store(false, std::sync::atomic::Ordering::Relaxed);
    initialize_fresh_var_ctr(fresh_base);
    let (before, _) = extract_module(chip, name.to_string(), &env, config());

    PORT_ORIGIN_AUDIT_ENABLED.store(true, std::sync::atomic::Ordering::Relaxed);
    initialize_fresh_var_ctr(fresh_base);
    let (after, _) = extract_module(chip, name.to_string(), &env, config());
    PORT_ORIGIN_AUDIT_ENABLED.store(false, std::sync::atomic::Ordering::Relaxed);

    assert_eq!(before.inputs, after.inputs, "audit must not change input values/order");
    assert_eq!(before.outputs, after.outputs, "audit must not change output values/order");
    assert_eq!(
        format!("{:?}", before.constraints),
        format!("{:?}", after.constraints),
        "audit must not change constraints or their order",
    );

    let audits = PORT_ORIGIN_ATTEMPTS.lock().unwrap();
    let attempt_log = audits.get(name).expect("audit recorded for the extracted module");
    let relevant = attempt_log
        .input_attempts
        .iter()
        .chain(&attempt_log.output_attempts)
        .filter(|event| {
            event.origin.starts_with("syscall_recv[")
                || event.origin.starts_with("syscall_result.")
        })
        .collect::<Vec<_>>();
    assert_eq!(relevant.len(), 13, "all attempted syscall roles, including aliases");
    assert_eq!(relevant.iter().filter(|event| event.retained).count(), 11);

    for index in 0..2 {
        let recv_name = format!("syscall_recv[{index}]");
        let at_name = format!("syscall_result.at[{index}]");
        let recv = relevant.iter().find(|event| event.origin == recv_name).expect("call timing");
        let at = relevant.iter().find(|event| event.origin == at_name).expect("result timing");
        assert_eq!(recv.variable_id, at.variable_id, "same variable underlying both roles");
        assert_eq!(recv.expression, at.expression, "same deduplication key");
        assert!(recv.retained, "first source role is retained");
        assert!(!at.retained, "second source role is not retained");
        println!(
            "MATHGRAPH_SYSLINUX_ALIAS role={at_name} variable_id={:?} key={}",
            at.variable_id, at.expression
        );
    }
    println!("MATHGRAPH_SYSLINUX_ORIGIN_AUDIT attempts=13 retained=11 duplicates=2");
}

/// Characterization only: the one-origin-per-retained-port contract says nothing about
/// whether a second source role using that same port must also be reported to readers.
fn check_direction(
    module_name: &str,
    direction: &str,
    ports: &[PicusExpr],
    attempts: &[PortOriginAttempt],
) -> usize {
    let emitted = ports.iter().map(ToString::to_string).collect::<Vec<_>>();
    let retained = attempts
        .iter()
        .filter(|attempt| attempt.retained)
        .map(|attempt| attempt.expression.as_str())
        .collect::<Vec<_>>();
    assert_eq!(
        retained,
        emitted.iter().map(String::as_str).collect::<Vec<_>>(),
        "{module_name}: {direction} retained attempts must match actual ports in order"
    );

    let mut first: BTreeMap<&str, Option<usize>> = BTreeMap::new();
    let mut aliases = 0;
    for attempt in attempts {
        assert!(
            attempt.variable_id.is_some(),
            "{module_name}: {direction} attempted a non-variable interface port"
        );
        if attempt.retained {
            assert!(
                first.insert(&attempt.expression, attempt.variable_id).is_none(),
                "{module_name}: {direction} retained the same port expression twice"
            );
        } else {
            assert_eq!(
                first.get(attempt.expression.as_str()),
                Some(&attempt.variable_id),
                "{module_name}: {direction} elided a role without a matching earlier port"
            );
            aliases += 1;
        }
    }
    aliases
}

#[test]
fn all_chip_origin_attempts_map_to_retained_ports() {
    let _guard = AUDIT_TEST_GUARD.lock().unwrap();
    let _ = set_field_modulus(0x7f00_0001);
    let chips = MipsAir::<Felt>::chips();
    PORT_ORIGIN_AUDIT_ENABLED.store(true, std::sync::atomic::Ordering::Relaxed);

    let mut modules = 0;
    let mut attempts = 0;
    let mut aliases = 0;
    let mut affected = Vec::new();
    for chip in &chips {
        let info = chip.picus_info();
        let selector = info
            .selector_indices
            .iter()
            .find(|(_, name)| chip.picus_selector_specialization_allowed(name))
            .map(|(col, _)| *col);
        let env = build_selector_env(&info, selector, true);
        let name = format!("{}__mathgraph_origin_census", chip.name());
        initialize_fresh_var_ctr(10 * chip.air.width() + 1024);
        let (module, _) = extract_module(chip, name.clone(), &env, config());

        let audit = PORT_ORIGIN_ATTEMPTS
            .lock()
            .unwrap()
            .get(&name)
            .cloned()
            .expect("all-chip extraction must record attempted origins");
        let input_aliases =
            check_direction(&name, "input", &module.inputs, &audit.input_attempts);
        let output_aliases =
            check_direction(&name, "output", &module.outputs, &audit.output_attempts);
        let chip_aliases = input_aliases + output_aliases;
        modules += 1;
        attempts += audit.input_attempts.len() + audit.output_attempts.len();
        aliases += chip_aliases;
        if chip_aliases != 0 {
            affected.push((chip.name(), input_aliases, output_aliases));
        }
    }
    PORT_ORIGIN_AUDIT_ENABLED.store(false, std::sync::atomic::Ordering::Relaxed);
    for (chip, ins, outs) in &affected {
        println!("MATHGRAPH_ORIGIN_CENSUS chip={chip} input_aliases={ins} output_aliases={outs}");
    }
    println!(
        "MATHGRAPH_ORIGIN_CENSUS_SUMMARY modules={modules} attempts={attempts} aliases={aliases} affected={}",
        affected.len()
    );
    assert!(modules >= 50, "the census must actually cover the machine's chip population");
    assert!(aliases >= 2, "SysLinux's two independently observed role aliases must remain visible");
}
