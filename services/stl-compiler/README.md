# STL Compiler

The STL (Signal Temporal Logic) Compiler is a core component of the CertifyEdge platform that translates STL specifications into Lean 4 definitions and SMT-LIB expressions for formal verification.

## Features

- **STL Parsing**: Parse STL specifications using ANTLR-generated grammar
- **Lean 4 Translation**: Generate Lean 4 definitions and proof skeletons
- **SMT-LIB Translation**: Generate SMT-LIB expressions for Z3 and CVC5 solvers
- **Round-trip Validation**: Validate AST ↔ JSON round-trip idempotence
- **Property-based Testing**: Comprehensive test coverage with proptest
- **Performance Optimization**: Fast compilation with caching and parallel execution

## Architecture

```
┌─────────────────┐    ┌─────────────────┐    ┌─────────────────┐
│   STL Input     │    │   STL Parser    │    │   AST           │
│   (Text)        │───▶│   (ANTLR)       │───▶│   (Rust)        │
└─────────────────┘    └─────────────────┘    └─────────────────┘
                                                           │
                                                           ▼
┌─────────────────┐    ┌─────────────────┐    ┌─────────────────┐
│   Lean 4        │◀───│   Lean 4        │◀───│   AST           │
│   Output        │    │   Translator    │    │   (Rust)        │
└─────────────────┘    └─────────────────┘    └─────────────────┘
                                                           │
                                                           ▼
┌─────────────────┐    ┌─────────────────┐    ┌─────────────────┐
│   SMT-LIB       │◀───│   SMT           │◀───│   AST           │
│   Output        │    │   Translator    │    │   (Rust)        │
└─────────────────┘    └─────────────────┘    └─────────────────┘
```

## Installation

### Prerequisites

- Rust 1.75.0 or later
- Lean 4.0.0 or later
- Z3 4.13.0 or later
- CVC5 1.2.0 or later

### Building with Bazel

```bash
# Build the STL compiler
bazel build //services/stl-compiler:stl_compiler

# Run tests
bazel test //services/stl-compiler:all_tests

# Run benchmarks
bazel test //services/stl-compiler:stl_compiler_benchmarks
```

### Building with Cargo

```bash
# Build the STL compiler
cargo build --release

# Run tests
cargo test

# Run benchmarks
cargo bench
```

## Usage

### Command Line Interface

```bash
# Compile STL specification
stl-compiler compile input.stl --output output_dir

# Validate STL specification
stl-compiler validate input.stl

# Start compiler server
stl-compiler serve --port 8080

# Show compiler information
stl-compiler info
```

### Example STL Specification

```stl
voltage_safety
// Voltage safety specification for power grid
voltage > 220 && current < 100
param: max_voltage real 240.0 Maximum voltage threshold
param: max_current real 100.0 Maximum current threshold
constraint: voltage_bounds bounds voltage <= 250.0
constraint: current_bounds bounds current <= 120.0
meta: author CertifyEdge Team
meta: version 1.0.0
```

### Temporal Operators

The STL compiler supports the following temporal operators:

- `G[0,10] φ` - Always (Globally) φ in time interval [0,10]
- `F[0,5] φ` - Eventually (Finally) φ in time interval [0,5]
- `φ U[0,10] ψ` - φ Until ψ in time interval [0,10]
- `X φ` - Next φ

### Logical Operators

- `φ && ψ` - Logical AND
- `φ || ψ` - Logical OR
- `!φ` - Logical NOT
- `φ -> ψ` - Implication
- `φ <-> ψ` - Equivalence

### Comparison Operators

- `variable > threshold` - Greater than
- `variable >= threshold` - Greater than or equal
- `variable < threshold` - Less than
- `variable <= threshold` - Less than or equal
- `variable == threshold` - Equal
- `variable != threshold` - Not equal

## Configuration

The STL compiler can be configured using a JSON configuration file:

```json
{
  "lean4": {
    "version": "4.0.0",
    "timeout_ms": 30000,
    "memory_limit_mb": 1024,
    "enable_native": true
  },
  "smt": {
    "default_solver": "z3",
    "enable_differential_testing": true,
    "timeout_ms": 10000,
    "z3": {
      "version": "4.13.0",
      "enabled": true
    },
    "cvc5": {
      "version": "1.2.0",
      "enabled": true
    }
  },
  "compilation": {
    "optimize": true,
    "debug": false,
    "warnings": true,
    "strict": true,
    "validate": true
  },
  "performance": {
    "max_compilation_time_ms": 60000,
    "max_memory_mb": 2048,
    "parallel": true,
    "num_threads": 8,
    "enable_cache": true
  }
}
```

## API

### Rust Library

```rust
use stl_compiler::{Compiler, CompilerConfig};

// Create compiler
let config = CompilerConfig::default();
let compiler = Compiler::new(config);

// Compile STL specification
let spec_text = "test_spec\nvoltage > 220";
let result = compiler.compile(spec_text).await?;

// Access results
println!("Lean 4 code: {}", result.lean4_output.lean4_code);
println!("SMT-LIB code: {}", result.smt_output.smt_lib_code);
println!("Compilation time: {}ms", result.stats.total_time_ms);
```

### gRPC Service

The STL compiler provides a gRPC service for integration with other components:

```protobuf
service STLCompiler {
  rpc Compile(CompileRequest) returns (CompileResponse);
  rpc Validate(ValidateRequest) returns (ValidateResponse);
  rpc GetInfo(InfoRequest) returns (InfoResponse);
}
```

## Testing

### Unit Tests

```bash
# Run unit tests
bazel test //services/stl-compiler:stl_compiler_unit_tests

# Run with coverage
bazel coverage //services/stl-compiler:stl_compiler_unit_tests
```

### Integration Tests

```bash
# Run integration tests
bazel test //services/stl-compiler:stl_compiler_integration_tests
```

### Property-based Tests

```bash
# Run property-based tests
bazel test //services/stl-compiler:stl_compiler_property_tests
```

### Performance Benchmarks

```bash
# Run benchmarks
bazel test //services/stl-compiler:stl_compiler_benchmarks
```

## Performance

The STL compiler is optimized for performance:

- **Compilation Time**: < 10ms per specification on M1 Pro
- **Memory Usage**: < 100MB for typical specifications
- **Parallel Execution**: Multi-threaded compilation
- **Caching**: Incremental compilation with cache
- **Optimization**: LTO and aggressive optimizations

## Quality Gates

The STL compiler enforces strict quality gates:

- **Code Coverage**: ≥ 95% coverage requirement
- **Property-based Testing**: Comprehensive input space coverage
- **Round-trip Validation**: AST ↔ JSON idempotence
- **Performance Regression**: Automated benchmark comparison
- **Static Analysis**: Clippy with strict warnings

## Security

The STL compiler implements security best practices:

- **Input Validation**: All inputs validated against schemas
- **Sandboxing**: SMT solvers run in isolated environments
- **Resource Limits**: Timeout and memory limits enforced
- **Dependency Scanning**: Automated vulnerability scanning
- **Audit Trail**: Complete compilation provenance

## Contributing

### Development Setup

1. Clone the repository
2. Install dependencies: `bazel sync`
3. Run tests: `bazel test //services/stl-compiler:all_tests`
4. Build: `bazel build //services/stl-compiler:stl_compiler`

### Code Style

- Follow Rust coding standards
- Use `rustfmt` for formatting
- Use `clippy` for linting
- Write comprehensive tests
- Document all public APIs

### Testing Guidelines

- Unit tests for all functions
- Integration tests for complete workflows
- Property-based tests for AST operations
- Performance benchmarks for critical paths
- Error handling tests for edge cases

## License

This project is licensed under the MIT License - see the [LICENSE](../LICENSE) file for details.

## References

- [Signal Temporal Logic](https://en.wikipedia.org/wiki/Signal_temporal_logic)
- [Lean 4](https://leanprover.github.io/lean4/)
- [SMT-LIB](http://smtlib.cs.uiowa.edu/)
- [Z3 Theorem Prover](https://github.com/Z3Prover/z3)
- [CVC5](https://cvc5.github.io/)
- [ANTLR](https://www.antlr.org/) 