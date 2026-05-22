# CertifyEdge PCS v0.1 runbook shortcuts (requires: cargo, optional: pcs from pcs-core)

CARGO ?= cargo
# Prefer python3; on Windows/Git Bash use: make PYTHON=python ...
PYTHON ?= python3
export PYTHON
SPEC ?= templates/hospital_lab/qc_release.stl
TRACE ?= tests/labtrust/valid_trace.json
CERT ?= trace_certificate.json

.PHONY: build test pcs-test runbook clean-checkout clean-checkout-certified fixtures release-run sync-pcs-core-rc check-pcs-core-rc sync-pcs-schemas sync-pcs-benchmark-schemas check-pcs-benchmark-schemas sync-pcs-hash-vectors check-pcs-hash-vectors sync-pcs-registry check-pcs-registry validate-profiles check-profiles write-handoff-fixture generate-certificate-benchmarks validate-certificate-benchmarks benchmark-certificates validate-benchmark-outputs pcs-bench-producer pcs-bench-producer-all-profiles validate-pcs-bench-ingest check-trace emit-certificate verify-certificate install-cli substrate-test bazel-pcs-test pcs-bench-producer-gate

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
	bash ./scripts/validate-certificate-benchmark-cases.sh
	bash ./scripts/check-pcs-optional.sh all
	$(CARGO) test -p certifyedge-integration --test certificate_benchmark_pcs_outputs -- --nocapture
	@if [ -d "../pcs-core/schemas" ] || [ -n "$${PCS_CORE_PATH:-}" ]; then bash ./scripts/check-pcs-benchmark-schemas-drift.sh; else echo "skip check-pcs-benchmark-schemas (no pcs-core checkout)"; fi
	@if [ -f "benchmark_runs/tool_use_safety/pcs_bench_ingest.v0.json" ]; then $(MAKE) validate-pcs-bench-ingest; else echo "skip validate-pcs-bench-ingest (run: make pcs-bench-producer-all-profiles)"; fi

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

sync-pcs-benchmark-schemas:
	bash ./scripts/sync-pcs-benchmark-schemas.sh

check-pcs-benchmark-schemas:
	@if [ -d "../pcs-core/schemas" ] || [ -n "$${PCS_CORE_PATH:-}" ]; then \
		bash ./scripts/check-pcs-benchmark-schemas-drift.sh; \
	else \
		$(PYTHON) scripts/merge-pcs-benchmark-defs.py 2>/dev/null || true; \
		echo "skip check-pcs-benchmark-schemas-drift (no pcs-core checkout)"; \
	fi

sync-pcs-hash-vectors:
	bash ./scripts/sync-pcs-hash-vectors.sh

check-pcs-hash-vectors:
	bash ./scripts/check-pcs-hash-vectors-drift.sh

sync-pcs-registry:
	bash ./scripts/sync-pcs-registry-contributions.sh

check-pcs-registry:
	bash ./scripts/check-pcs-registry-contribution-drift.sh

generate-certificate-benchmarks:
	$(PYTHON) scripts/generate-certificate-benchmark-cases.py

validate-certificate-benchmarks: build
	bash ./scripts/validate-certificate-benchmark-cases.sh
	bash ./scripts/check-certificate-benchmark-cases-drift.sh
	@if [ -d "../pcs-core/schemas" ] || [ -n "$${PCS_CORE_PATH:-}" ]; then bash ./scripts/check-pcs-benchmark-schemas-drift.sh; else echo "skip check-pcs-benchmark-schemas (no pcs-core checkout)"; fi

BENCHMARK_PCS_CORE_VALIDATE := $(if $(wildcard ../pcs-core/schemas),--validate-pcs-core-output ../pcs-core,)

benchmark-certificates: build generate-certificate-benchmarks validate-certificate-benchmarks
	$(CARGO) run -p certifyedge -- benchmark certificates \
		--profile hospital_lab.qc_release \
		--cases benchmarks/certificates/hospital_lab_qc_release \
		--out benchmark_runs/hospital_lab_qc_release \
		--json-summary $(BENCHMARK_PCS_CORE_VALIDATE)
	$(CARGO) run -p certifyedge -- benchmark certificates \
		--profile agent_tool_use.safety_v0 \
		--cases benchmarks/certificates/tool_use_safety \
		--out benchmark_runs/tool_use_safety \
		--json-summary $(BENCHMARK_PCS_CORE_VALIDATE)
	$(CARGO) run -p certifyedge -- benchmark certificates \
		--profile scientific_computation.reproducibility_v0 \
		--cases benchmarks/certificates/computation_reproducibility \
		--out benchmark_runs/computation_reproducibility \
		--json-summary $(BENCHMARK_PCS_CORE_VALIDATE)

validate-benchmark-outputs: build
	bash ./scripts/validate-certificate-benchmark-outputs.sh

PCS_BENCH_PCS_CORE_VALIDATE := $(if $(wildcard ../pcs-core/schemas),--validate-pcs-core-output ../pcs-core,)

pcs-bench-producer: build generate-certificate-benchmarks validate-certificate-benchmarks
	$(CARGO) run -p certifyedge -- benchmark certificates \
		--profile agent_tool_use.safety_v0 \
		--cases benchmarks/certificates/tool_use_safety \
		--out benchmark_runs/tool_use_safety \
		--json-summary $(PCS_BENCH_PCS_CORE_VALIDATE)
	$(MAKE) validate-benchmark-outputs
	$(MAKE) validate-pcs-bench-ingest-release-grade

pcs-bench-producer-all-profiles: benchmark-certificates validate-benchmark-outputs validate-pcs-bench-ingest

validate-pcs-bench-ingest-release-grade:
	bash ./scripts/validate-pcs-bench-ingest-consumer.sh \
		benchmark_runs/tool_use_safety/pcs_bench_ingest.v0.json --release-grade

pcs-bench-producer-gate:
	bash ./scripts/pcs-bench-producer.sh

validate-pcs-bench-ingest:
	@for suite in hospital_lab_qc_release tool_use_safety computation_reproducibility; do \
		bash ./scripts/validate-pcs-bench-ingest-consumer.sh \
			"benchmark_runs/$$suite/pcs_bench_ingest.v0.json" --release-grade; \
	done

validate-profiles: build
	$(CARGO) run -p certifyedge -- profiles list
	$(CARGO) run -p certifyedge -- profiles validate templates/profiles/hospital_lab.qc_release.json
	$(CARGO) run -p certifyedge -- profiles validate templates/profiles/hospital_lab.no_release_before_qc.json
	$(CARGO) run -p certifyedge -- profiles validate templates/profiles/agent_tool_use.safety_v0.json
	$(CARGO) run -p certifyedge -- profiles validate templates/profiles/scientific_computation.reproducibility_v0.json

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
