//! Opt-in origin-attempt audit of a real chip; does not require a Lean proof replay.

use p3_air::BaseAir;
use zkm_core_machine::MipsAir;
use zkm_pcs::MachineAir;
use zkm_picus::{
    pcl::{initialize_fresh_var_ctr, set_field_modulus, Felt},
    picus_builder::{
        build_selector_env, extract_module, ColumnOutputMode, ExtractionConfig,
        ShrCarrySummaryMode, SubmoduleMode, PORT_ORIGIN_ATTEMPTS, PORT_ORIGIN_AUDIT_ENABLED,
    },
};

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
