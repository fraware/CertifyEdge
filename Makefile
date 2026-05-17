# CertifyEdge PCS v0.1 runbook shortcuts (requires: cargo, optional: pcs from pcs-core)

CARGO ?= cargo
SPEC ?= templates/hospital_lab/qc_release.stl
TRACE ?= tests/labtrust/valid_trace.json
CERT ?= trace_certificate.json

.PHONY: build test pcs-test runbook check-trace emit-certificate verify-certificate install-cli

build:
	$(CARGO) build -p certifyedge

install-cli:
	./scripts/install-certifyedge.sh

test:
	$(CARGO) test -p certifyedge-integration -- --nocapture
	$(CARGO) clippy -p labtrust-adapter -p pcs-certificate -p certifyedge -- -D warnings

pcs-test: build test

runbook: build
	./scripts/pcs-runbook.sh

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
