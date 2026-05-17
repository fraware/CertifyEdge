# CertifyEdge PCS v0.1 runbook shortcuts (requires: cargo, optional: pcs from pcs-core)

CARGO ?= cargo
SPEC ?= templates/hospital_lab/qc_release.stl
TRACE ?= tests/labtrust/valid_trace.json
CERT ?= trace_certificate.json

.PHONY: build test pcs-test runbook clean-checkout clean-checkout-certified fixtures release-run sync-pcs-core-rc check-trace emit-certificate verify-certificate install-cli substrate-test bazel-pcs-test

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

pcs-test: build test

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
