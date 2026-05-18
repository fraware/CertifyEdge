# CertifyEdge PCS v0.1 runbook shortcuts (requires: cargo, optional: pcs from pcs-core)

CARGO ?= cargo
SPEC ?= templates/hospital_lab/qc_release.stl
TRACE ?= tests/labtrust/valid_trace.json
CERT ?= trace_certificate.json

.PHONY: build test pcs-test runbook clean-checkout clean-checkout-certified fixtures release-run sync-pcs-core-rc check-pcs-core-rc sync-pcs-schemas sync-pcs-hash-vectors check-pcs-hash-vectors check-pcs-registry validate-profiles check-profiles write-handoff-fixture check-trace emit-certificate verify-certificate install-cli substrate-test bazel-pcs-test

build:
	$(CARGO) build -p certifyedge

install-cli:
	./scripts/install-certifyedge.sh

test:
	$(CARGO) test -p certifyedge-integration -- --nocapture
	$(CARGO) clippy -p labtrust-adapter -p pcs-certificate -p certifyedge -- -D warnings

substrate-test:
	./scripts/test-substrate.sh

bazel-pcs-test:
	./scripts/bazel-pcs-test.sh

check-profiles: validate-profiles

pcs-test: build test
	bash ./scripts/validate-profiles.sh
	bash ./scripts/check-pcs-optional.sh all

runbook: build
	./scripts/pcs-runbook.sh

clean-checkout: build
	./scripts/pcs-v01-clean-checkout.sh

clean-checkout-certified: build
	./scripts/pcs-v01-clean-checkout.sh --through-certified

fixtures: build
	cargo test -p certifyedge-integration write_fixtures -- --ignored --nocapture

release-run: build
	bash ./scripts/build-release-run.sh

sync-pcs-core-rc:
	bash ./scripts/sync-pcs-core-rc-fixtures.sh

sync-pcs-schemas:
	bash ./scripts/sync-pcs-schemas.sh

sync-pcs-hash-vectors:
	bash ./scripts/sync-pcs-hash-vectors.sh

check-pcs-hash-vectors:
	bash ./scripts/check-pcs-hash-vectors-drift.sh

check-pcs-registry:
	bash ./scripts/check-pcs-registry-contribution-drift.sh

validate-profiles: build
	$(CARGO) run -p certifyedge -- profiles list
	$(CARGO) run -p certifyedge -- profiles validate templates/profiles/hospital_lab.qc_release.json
	$(CARGO) run -p certifyedge -- profiles validate templates/profiles/hospital_lab.no_release_before_qc.json
	$(CARGO) run -p certifyedge -- profiles validate templates/profiles/agent_tool_use.safety_v0.json

check-pcs-core-rc:
	bash ./scripts/check-pcs-core-rc-drift.sh

write-handoff-fixture: build
	bash ./scripts/write-labtrust-handoff-fixture.sh

check-trace: build
	$(CARGO) run -p certifyedge -- check-trace --spec $(SPEC) --trace $(TRACE)

emit-certificate: build
	$(CARGO) run -p certifyedge -- emit-pcs-certificate --spec $(SPEC) --trace $(TRACE) --out $(CERT)

emit-certificate-release: build
	$(CARGO) run -p certifyedge -- --release-mode emit-pcs-certificate --spec $(SPEC) --trace $(TRACE) --out $(CERT)

verify-certificate: build
	$(CARGO) run -p certifyedge -- verify-certificate $(CERT)

.PHONY: explain-counterexample
explain-counterexample: build
	$(CARGO) run -p certifyedge -- explain-counterexample target/cli_reject/counterexample.json
