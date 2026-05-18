//! Property profile registry (`templates/profiles/<property_id>.json`).

use std::path::{Path, PathBuf};

use serde::Deserialize;

#[derive(Debug, Clone, Deserialize)]
pub struct PropertyProfile {
    pub property_id: String,
    pub template: String,
    pub input_trace_artifact: String,
    pub output_certificate_artifact: String,
    pub counterexample_artifact: String,
}

pub fn profile_path(property_id: &str, certifyedge_root: &Path) -> PathBuf {
    certifyedge_root
        .join("templates/profiles")
        .join(format!("{property_id}.json"))
}

pub fn load_property_profile(
    property_id: &str,
    certifyedge_root: &Path,
) -> Result<PropertyProfile, String> {
    let path = profile_path(property_id, certifyedge_root);
    let text = std::fs::read_to_string(&path)
        .map_err(|e| format!("property profile not found ({}): {e}", path.display()))?;
    let profile: PropertyProfile = serde_json::from_str(&text)
        .map_err(|e| format!("invalid property profile {}: {e}", path.display()))?;
    if profile.property_id != property_id {
        return Err(format!(
            "property profile {} declares property_id {}, expected {}",
            path.display(),
            profile.property_id,
            property_id
        ));
    }
    Ok(profile)
}

pub fn spec_path_for_property_id(
    property_id: &str,
    certifyedge_root: &Path,
) -> Result<PathBuf, String> {
    let profile = load_property_profile(property_id, certifyedge_root)?;
    let path = certifyedge_root.join(&profile.template);
    if !path.is_file() {
        return Err(format!("property spec not found: {}", path.display()));
    }
    Ok(path)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn hospital_lab_qc_release_profile_loads() {
        let root = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
        let profile =
            load_property_profile("hospital_lab.qc_release", &root).expect("profile loads");
        assert_eq!(profile.input_trace_artifact, "LabTrust.Trace.v0");
        assert_eq!(profile.output_certificate_artifact, "TraceCertificate.v0");
        let spec = spec_path_for_property_id("hospital_lab.qc_release", &root).unwrap();
        assert!(spec.ends_with("qc_release.stl"));
    }
}
