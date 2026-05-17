//! PCS trace certificate status transitions (Phase 2 policy).

pub const STATUS_CERTIFICATE_PENDING: &str = "CertificatePending";
pub const STATUS_CERTIFICATE_CHECKED: &str = "CertificateChecked";
pub const STATUS_REJECTED: &str = "Rejected";
pub const STATUS_STALE: &str = "Stale";

/// Validate an intended certificate status transition.
pub fn validate_certificate_status_transition(
    from: &str,
    to: &str,
    release_mode: bool,
) -> Result<(), String> {
    if from == to {
        return Ok(());
    }
    if release_mode && from == STATUS_REJECTED {
        return Err(format!(
            "release mode: {STATUS_REJECTED} is terminal (cannot transition to {to})"
        ));
    }
    match (from, to) {
        (STATUS_CERTIFICATE_PENDING, STATUS_CERTIFICATE_CHECKED) => Ok(()),
        (STATUS_CERTIFICATE_PENDING, STATUS_REJECTED) => Ok(()),
        (STATUS_CERTIFICATE_CHECKED, STATUS_STALE) => Ok(()),
        _ => Err(format!(
            "invalid certificate status transition: {from} -> {to}"
        )),
    }
}

pub fn is_terminal_certificate_status(status: &str, release_mode: bool) -> bool {
    release_mode && status == STATUS_REJECTED
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pending_to_checked_allowed() {
        validate_certificate_status_transition(
            STATUS_CERTIFICATE_PENDING,
            STATUS_CERTIFICATE_CHECKED,
            true,
        )
        .unwrap();
    }

    #[test]
    fn rejected_terminal_in_release_mode() {
        assert!(is_terminal_certificate_status(STATUS_REJECTED, true));
        assert!(validate_certificate_status_transition(
            STATUS_REJECTED,
            STATUS_CERTIFICATE_CHECKED,
            true
        )
        .is_err());
    }
}
