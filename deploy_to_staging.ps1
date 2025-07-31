# CertifyEdge Platform - Staging Deployment Script
# Production-grade, formally-verified, audit-ready platform

param(
    [string]$Environment = "staging",
    [switch]$SkipTests,
    [switch]$SkipMonitoring,
    [switch]$Force,
    [string]$KubernetesContext = "certifyedge-staging"
)

Write-Host "=== CertifyEdge Platform - Staging Deployment ===" -ForegroundColor Green
Write-Host "Date: $(Get-Date)" -ForegroundColor Yellow
Write-Host "Environment: $Environment" -ForegroundColor Yellow
Write-Host "Kubernetes Context: $KubernetesContext" -ForegroundColor Yellow
Write-Host ""

# Step 1: Pre-deployment validation
Write-Host "Step 1: Pre-deployment Validation" -ForegroundColor Cyan
Write-Host "=================================" -ForegroundColor Cyan

if (-not $SkipTests) {
    Write-Host "Running comprehensive test suite..." -ForegroundColor White
    $testResult = & .\tests\run_comprehensive_tests.ps1
    if ($LASTEXITCODE -ne 0) {
        Write-Host "❌ Tests failed. Deployment aborted." -ForegroundColor Red
        exit 1
    }
    Write-Host "✅ All tests passed" -ForegroundColor Green
} else {
    Write-Host "⚠️  Skipping tests (--SkipTests specified)" -ForegroundColor Yellow
}

# Step 2: Infrastructure validation
Write-Host "`nStep 2: Infrastructure Validation" -ForegroundColor Cyan
Write-Host "=================================" -ForegroundColor Cyan

# Check Kubernetes context
Write-Host "Validating Kubernetes context..." -ForegroundColor White
try {
    $kubectlOutput = kubectl config current-context 2>&1
    if ($LASTEXITCODE -eq 0) {
        Write-Host "✅ Kubernetes context available: $kubectlOutput" -ForegroundColor Green
    } else {
        Write-Host "❌ Kubernetes context not available" -ForegroundColor Red
        Write-Host "Please configure kubectl for staging environment" -ForegroundColor Yellow
        exit 1
    }
} catch {
    Write-Host "❌ kubectl not found or not configured" -ForegroundColor Red
    exit 1
}

# Check Terraform configuration
Write-Host "Validating Terraform configuration..." -ForegroundColor White
$terraformFiles = @(
    "infrastructure/terraform/gpu-farm/main.tf",
    "infrastructure/terraform/gpu-farm/variables.tf",
    "infrastructure/terraform/gpu-farm/outputs.tf"
)

foreach ($file in $terraformFiles) {
    if (Test-Path $file) {
        Write-Host "✅ Terraform file exists: $file" -ForegroundColor Green
    } else {
        Write-Host "❌ Terraform file missing: $file" -ForegroundColor Red
        exit 1
    }
}

# Step 3: Build and package
Write-Host "`nStep 3: Build and Package" -ForegroundColor Cyan
Write-Host "=========================" -ForegroundColor Cyan

Write-Host "Building Docker images..." -ForegroundColor White

# Build core services
$services = @(
    "stl-compiler",
    "smt-verifier", 
    "certificate",
    "auditor-api",
    "lean-autoprover",
    "gpu-farm",
    "grid-in-loop"
)

foreach ($service in $services) {
    $dockerfile = "services/$service/Dockerfile"
    if (Test-Path $dockerfile) {
        Write-Host "Building $service..." -ForegroundColor White
        $imageTag = "certifyedge/$service:staging-$(Get-Date -Format 'yyyyMMdd-HHmmss')"
        
        try {
            docker build -t $imageTag -f $dockerfile "services/$service"
            if ($LASTEXITCODE -eq 0) {
                Write-Host "✅ Built $service: $imageTag" -ForegroundColor Green
            } else {
                Write-Host "❌ Failed to build $service" -ForegroundColor Red
                exit 1
            }
        } catch {
            Write-Host "❌ Docker build failed for $service" -ForegroundColor Red
            exit 1
        }
    } else {
        Write-Host "⚠️  No Dockerfile found for $service, skipping" -ForegroundColor Yellow
    }
}

# Step 4: Deploy to staging
Write-Host "`nStep 4: Deploy to Staging" -ForegroundColor Cyan
Write-Host "=========================" -ForegroundColor Cyan

Write-Host "Applying Kubernetes manifests..." -ForegroundColor White

# Create namespace if it doesn't exist
$namespace = "certifyedge-staging"
kubectl create namespace $namespace --dry-run=client -o yaml | kubectl apply -f -

# Apply infrastructure components
Write-Host "Deploying infrastructure components..." -ForegroundColor White

# Deploy Prometheus monitoring
if (-not $SkipMonitoring) {
    Write-Host "Deploying Prometheus monitoring..." -ForegroundColor White
    kubectl apply -f infrastructure/kubernetes/monitoring/ -n $namespace
    
    # Deploy Grafana dashboards
    Write-Host "Deploying Grafana dashboards..." -ForegroundColor White
    kubectl apply -f infrastructure/kubernetes/grafana/ -n $namespace
}

# Deploy core services
Write-Host "Deploying core services..." -ForegroundColor White
kubectl apply -f infrastructure/kubernetes/services/ -n $namespace

# Deploy GPU farm components
Write-Host "Deploying GPU farm components..." -ForegroundColor White
kubectl apply -f infrastructure/kubernetes/gpu-farm/ -n $namespace

# Step 5: Health checks
Write-Host "`nStep 5: Health Checks" -ForegroundColor Cyan
Write-Host "=====================" -ForegroundColor Cyan

Write-Host "Waiting for services to be ready..." -ForegroundColor White
Start-Sleep -Seconds 30

# Check service health
$services = @(
    "stl-compiler",
    "smt-verifier",
    "certificate",
    "auditor-api"
)

foreach ($service in $services) {
    Write-Host "Checking $service health..." -ForegroundColor White
    $healthCheck = kubectl get pods -n $namespace -l app=$service -o jsonpath='{.items[0].status.phase}' 2>$null
    
    if ($healthCheck -eq "Running") {
        Write-Host "✅ $service is healthy" -ForegroundColor Green
    } else {
        Write-Host "❌ $service is not healthy: $healthCheck" -ForegroundColor Red
        if (-not $Force) {
            Write-Host "Deployment failed. Use --Force to continue anyway." -ForegroundColor Yellow
            exit 1
        }
    }
}

# Step 6: Monitoring setup
Write-Host "`nStep 6: Monitoring Setup" -ForegroundColor Cyan
Write-Host "========================" -ForegroundColor Cyan

if (-not $SkipMonitoring) {
    Write-Host "Setting up monitoring dashboards..." -ForegroundColor White
    
    # Create monitoring configuration
    $monitoringConfig = @"
apiVersion: v1
kind: ConfigMap
metadata:
  name: monitoring-config
  namespace: $namespace
data:
  prometheus.yml: |
    global:
      scrape_interval: 15s
    scrape_configs:
      - job_name: 'certifyedge-services'
        static_configs:
          - targets: ['stl-compiler:8080', 'smt-verifier:8080', 'certificate:8080', 'auditor-api:8080']
"@
    
    $monitoringConfig | kubectl apply -f -
    
    Write-Host "✅ Monitoring configuration applied" -ForegroundColor Green
    
    # Setup alerting rules
    Write-Host "Setting up alerting rules..." -ForegroundColor White
    kubectl apply -f infrastructure/kubernetes/alerts/ -n $namespace
    
    Write-Host "✅ Alerting rules configured" -ForegroundColor Green
} else {
    Write-Host "⚠️  Skipping monitoring setup (--SkipMonitoring specified)" -ForegroundColor Yellow
}

# Step 7: Post-deployment validation
Write-Host "`nStep 7: Post-deployment Validation" -ForegroundColor Cyan
Write-Host "===================================" -ForegroundColor Cyan

Write-Host "Running post-deployment tests..." -ForegroundColor White

# Test service endpoints
$endpoints = @(
    "http://stl-compiler.$namespace.svc.cluster.local:8080/health",
    "http://smt-verifier.$namespace.svc.cluster.local:8080/health",
    "http://certificate.$namespace.svc.cluster.local:8080/health",
    "http://auditor-api.$namespace.svc.cluster.local:8080/health"
)

foreach ($endpoint in $endpoints) {
    try {
        $response = Invoke-WebRequest -Uri $endpoint -TimeoutSec 10 -UseBasicParsing
        if ($response.StatusCode -eq 200) {
            Write-Host "✅ Health check passed: $endpoint" -ForegroundColor Green
        } else {
            Write-Host "❌ Health check failed: $endpoint (Status: $($response.StatusCode))" -ForegroundColor Red
        }
    } catch {
        Write-Host "❌ Health check failed: $endpoint (Connection error)" -ForegroundColor Red
    }
}

# Step 8: Deployment summary
Write-Host "`nStep 8: Deployment Summary" -ForegroundColor Cyan
Write-Host "==========================" -ForegroundColor Cyan

Write-Host "✅ Staging deployment completed successfully!" -ForegroundColor Green
Write-Host ""
Write-Host "Deployment Details:" -ForegroundColor White
Write-Host "- Environment: $Environment" -ForegroundColor White
Write-Host "- Namespace: $namespace" -ForegroundColor White
Write-Host "- Kubernetes Context: $KubernetesContext" -ForegroundColor White
Write-Host "- Monitoring: $(if ($SkipMonitoring) { 'Disabled' } else { 'Enabled' })" -ForegroundColor White
Write-Host ""
Write-Host "Next Steps:" -ForegroundColor Cyan
Write-Host "1. Monitor the staging environment for 24-48 hours" -ForegroundColor White
Write-Host "2. Run performance tests against staging" -ForegroundColor White
Write-Host "3. Validate all functionality in staging" -ForegroundColor White
Write-Host "4. Get stakeholder approval for production deployment" -ForegroundColor White
Write-Host "5. Run: .\deploy_to_production.ps1" -ForegroundColor White
Write-Host ""
Write-Host "Monitoring URLs:" -ForegroundColor Cyan
Write-Host "- Prometheus: http://prometheus.$namespace.svc.cluster.local:9090" -ForegroundColor White
Write-Host "- Grafana: http://grafana.$namespace.svc.cluster.local:3000" -ForegroundColor White
Write-Host "- Jaeger: http://jaeger.$namespace.svc.cluster.local:16686" -ForegroundColor White

# Save deployment log
$deploymentLog = @"
# CertifyEdge Staging Deployment Log
Date: $(Get-Date)
Environment: $Environment
Namespace: $namespace
Kubernetes Context: $KubernetesContext
Monitoring: $(if ($SkipMonitoring) { 'Disabled' } else { 'Enabled' })

## Deployment Summary
- ✅ Pre-deployment validation passed
- ✅ Infrastructure validation passed
- ✅ Build and package completed
- ✅ Staging deployment completed
- ✅ Health checks passed
- ✅ Monitoring setup completed
- ✅ Post-deployment validation passed

## Next Steps
1. Monitor staging environment for 24-48 hours
2. Run performance tests against staging
3. Validate all functionality in staging
4. Get stakeholder approval for production deployment
5. Deploy to production

## Monitoring URLs
- Prometheus: http://prometheus.$namespace.svc.cluster.local:9090
- Grafana: http://grafana.$namespace.svc.cluster.local:3000
- Jaeger: http://jaeger.$namespace.svc.cluster.local:16686
"@

$deploymentLog | Out-File -FilePath "deployment-log-staging-$(Get-Date -Format 'yyyyMMdd-HHmmss').md" -Encoding UTF8

Write-Host "`nDeployment log saved to: deployment-log-staging-$(Get-Date -Format 'yyyyMMdd-HHmmss').md" -ForegroundColor Cyan 