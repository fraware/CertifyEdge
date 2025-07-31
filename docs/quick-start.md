# CertifyEdge Quick Start Guide

## Overview

CertifyEdge is a production-grade, formally-verified platform for certifying AI agents in power grid applications. This guide will help you set up the development environment and get started with the codebase.

## Prerequisites

### System Requirements
- **OS**: Linux (Ubuntu 20.04+), macOS (10.15+), or Windows 10/11 with WSL2
- **RAM**: 16GB minimum, 32GB recommended
- **Storage**: 50GB free space
- **CPU**: 8 cores minimum, 16 cores recommended

### Required Software
- **Bazel**: 7.0.0 (automatically managed by Bazelisk)
- **Rust**: 1.75.0
- **Node.js**: 20.x
- **Python**: 3.11
- **Lean 4**: 4.0.0
- **Docker**: 20.10+ (for containerized development)

## Installation

### 1. Clone the Repository
```bash
git clone https://github.com/fraware/CertifyEdge.git
cd CertifyEdge
```

### 2. Install Bazelisk
```bash
# Linux/macOS
curl -L https://github.com/bazelbuild/bazelisk/releases/latest/download/bazelisk-$(uname -s)-$(uname -m) -o bazelisk
chmod +x bazelisk
sudo mv bazelisk /usr/local/bin/

# Windows (with Chocolatey)
choco install bazelisk

# Or download from GitHub releases
```

### 3. Install Rust
```bash
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
source ~/.cargo/env
rustup default 1.75.0
rustup component add clippy rustfmt
```

### 4. Install Node.js
```bash
# Using nvm (recommended)
curl -o- https://raw.githubusercontent.com/nvm-sh/nvm/v0.39.0/install.sh | bash
source ~/.bashrc
nvm install 20
nvm use 20

# Or using package manager
# Ubuntu/Debian
curl -fsSL https://deb.nodesource.com/setup_20.x | sudo -E bash -
sudo apt-get install -y nodejs

# macOS
brew install node@20
```

### 5. Install Python
```bash
# Using pyenv (recommended)
curl https://pyenv.run | bash
source ~/.bashrc
pyenv install 3.11.0
pyenv global 3.11.0

# Or using package manager
# Ubuntu/Debian
sudo apt-get install python3.11 python3.11-venv python3.11-pip

# macOS
brew install python@3.11
```

### 6. Install Lean 4
```bash
# Download and install Lean 4
wget https://github.com/leanprover/lean4/releases/download/v4.0.0/lean-4.0.0-linux.tar.gz
tar -xzf lean-4.0.0-linux.tar.gz
echo 'export PATH="$PWD/lean-4.0.0-linux/bin:$PATH"' >> ~/.bashrc
source ~/.bashrc
```

### 7. Install Docker
```bash
# Ubuntu/Debian
curl -fsSL https://get.docker.com -o get-docker.sh
sudo sh get-docker.sh
sudo usermod -aG docker $USER

# macOS
brew install --cask docker

# Windows
# Download Docker Desktop from https://www.docker.com/products/docker-desktop
```

## Development Setup

### 1. Verify Installation
```bash
# Check all tools are available
bazel --version
rustc --version
node --version
python3 --version
lean --version
docker --version
```

### 2. Build the Project
```bash
# First build (may take 10-15 minutes)
bazel build //...

# Verify the build works
bazel test //... --test_tag_filters=unit
```

### 3. Run Development Environment
```bash
# Start development servers
bazel run //web:dev
bazel run //services/certificate-service:dev
bazel run //services/smt-verifier:dev
```

## Project Structure

```
CertifyEdge/
├── WORKSPACE                 # Bazel workspace configuration
├── BUILD                     # Root package definition
├── .bazelrc                  # Bazel configuration
├── .bazelversion            # Pinned Bazel version
├── services/                 # Microservices (Rust)
│   ├── stl-compiler/        # STL to Lean 4 compiler
│   ├── lean-autoprover/     # Lean 4 autoprover plugin
│   ├── smt-verifier/        # SMT verification service
│   ├── certificate-service/  # Certificate management
│   ├── provenance-service/   # Provenance tracking
│   ├── policy-engine/        # OPA policy engine
│   ├── gpu-farm/            # GPU verification farm
│   ├── auditor/             # Audit service
│   └── cert-mgmt/           # Certificate management
├── web/                      # Frontend (TypeScript + Next.js)
│   ├── components/          # React components
│   ├── pages/               # Next.js pages
│   ├── styles/              # CSS/SCSS styles
│   └── public/              # Static assets
├── tools/                    # Development tools
│   ├── python/              # Python utilities
│   ├── rust/                # Rust utilities
│   └── scripts/             # Shell scripts
├── tests/                    # Testing infrastructure
│   ├── unit/                # Unit tests
│   ├── integration/         # Integration tests
│   ├── property/            # Property-based tests
│   ├── formal/              # Formal verification tests
│   ├── performance/         # Performance tests
│   ├── security/            # Security tests
│   ├── e2e/                 # End-to-end tests
│   ├── grid-in-loop/        # Grid simulation tests
│   ├── mutation/            # Mutation tests
│   ├── contract/            # Contract tests
│   └── differential/        # Differential tests
├── infrastructure/           # Deployment configs
│   ├── terraform/           # Infrastructure as code
│   ├── kubernetes/          # K8s manifests
│   ├── helm/                # Helm charts
│   └── docker/              # Docker configurations
└── docs/                     # Documentation
```

## Common Commands

### Building
```bash
# Build all targets
bazel build //...

# Build specific service
bazel build //services/certificate-service:all

# Build with optimizations
bazel build --config=release //...
```

### Testing
```bash
# Run all tests
bazel test //...

# Run specific test types
bazel test //... --test_tag_filters=unit
bazel test //... --test_tag_filters=property
bazel test //... --test_tag_filters=formal

# Run with coverage
bazel coverage //... --combined_report=lcov
```

### Development
```bash
# Start development server
bazel run //web:dev

# Run specific service
bazel run //services/certificate-service:dev

# Format code
bazel run //tools:format

# Lint code
bazel run //tools:lint
```

### Security
```bash
# Run security scans
bazel test //... --test_tag_filters=security

# Audit dependencies
bazel run //tools:audit

# Generate SBOM
bazel build //... --aspects @rules_security//security:defs.bzl%sbom_aspect
```

## Quality Gates

### Code Quality
- **Coverage**: Minimum 95% code coverage
- **Linting**: All linters must pass
- **Formatting**: Code must be properly formatted
- **Documentation**: All public APIs must be documented

### Security
- **Vulnerabilities**: Zero critical/high vulnerabilities
- **Dependencies**: All dependencies audited
- **Signatures**: All artifacts cryptographically signed
- **Compliance**: Meets regulatory requirements

### Performance
- **Build Time**: Full build < 10 minutes
- **Test Time**: All tests < 30 minutes
- **API Latency**: P99 < 100ms
- **Resource Usage**: Efficient memory and CPU usage

## Troubleshooting

### Common Issues

#### Build Failures
```bash
# Clean and rebuild
bazel clean --expunge
bazel build //...

# Check for missing dependencies
bazel query --output=location //...
```

#### Test Failures
```bash
# Run tests with verbose output
bazel test //... --test_output=errors --verbose_failures

# Check test logs
bazel test //... --test_output=all
```

#### Performance Issues
```bash
# Check Bazel performance
bazel analyze --output=text //...

# Profile build
bazel build --profile=build.profile //...
```

### Getting Help

1. **Issues**: Create an issue on GitHub
2. **Discussions**: Use GitHub Discussions for questions

## Next Steps

1. **Read the Architecture**: Review the [architecture documentation](docs/architecture/)
2. **Explore Services**: Start with the [certificate service](services/certificate-service/)
3. **Run Tests**: Execute the [testing suite](tests/)
4. **Contribute**: Follow the [contributing guidelines](CONTRIBUTING.md)

## Support

- **GitHub Issues**: [https://github.com/fraware/CertifyEdge/issues](https://github.com/fraware/CertifyEdge/issues)
- **Documentation**: [https://github.com/fraware/CertifyEdge/docs](https://github.com/fraware/CertifyEdge/docs)
- **Discussions**: [https://github.com/fraware/CertifyEdge/discussions](https://github.com/fraware/CertifyEdge/discussions)

## License

This project is licensed under the MIT License - see the [LICENSE](LICENSE) file for details. 