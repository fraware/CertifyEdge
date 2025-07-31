# CertifyEdge GPU Farm Infrastructure
# 
# This Terraform configuration sets up a Kubernetes-based GPU farm with:
# - Autoscaling spot GPU nodes (A10/A100) using Karpenter
# - Budget caps and cost management
# - Node-local SSD cache for Lean OLE cache
# - Canary deployment with chaos engineering

terraform {
  required_version = ">= 1.0"
  required_providers {
    azurerm = {
      source  = "hashicorp/azurerm"
      version = "~> 3.0"
    }
    kubernetes = {
      source  = "hashicorp/kubernetes"
      version = "~> 2.0"
    }
    helm = {
      source  = "hashicorp/helm"
      version = "~> 2.0"
    }
  }
}

# Variables
variable "resource_group_name" {
  description = "Name of the resource group"
  type        = string
  default     = "certifyedge-gpu-farm"
}

variable "location" {
  description = "Azure region"
  type        = string
  default     = "East US"
}

variable "cluster_name" {
  description = "Name of the AKS cluster"
  type        = string
  default     = "certifyedge-gpu-cluster"
}

variable "gpu_node_pool_name" {
  description = "Name of the GPU node pool"
  type        = string
  default     = "gpunodepool"
}

variable "budget_limit" {
  description = "Monthly budget limit in USD"
  type        = number
  default     = 5000
}

variable "max_gpu_nodes" {
  description = "Maximum number of GPU nodes"
  type        = number
  default     = 20
}

variable "spot_instance_percentage" {
  description = "Percentage of spot instances"
  type        = number
  default     = 80
}

# Data sources
data "azurerm_client_config" "current" {}

data "azurerm_resource_group" "main" {
  name = var.resource_group_name
}

# Resource group
resource "azurerm_resource_group" "main" {
  count    = var.resource_group_name == "certifyedge-gpu-farm" ? 1 : 0
  name     = var.resource_group_name
  location = var.location
  
  tags = {
    Environment = "Production"
    Project     = "CertifyEdge"
    Component   = "GPU-Farm"
  }
}

# Virtual network
resource "azurerm_virtual_network" "main" {
  name                = "${var.cluster_name}-vnet"
  resource_group_name = data.azurerm_resource_group.main.name
  location            = data.azurerm_resource_group.main.location
  address_space       = ["10.0.0.0/16"]
  
  tags = {
    Environment = "Production"
    Project     = "CertifyEdge"
  }
}

# Subnet for AKS
resource "azurerm_subnet" "aks" {
  name                 = "${var.cluster_name}-subnet"
  resource_group_name  = data.azurerm_resource_group.main.name
  virtual_network_name = azurerm_virtual_network.main.name
  address_prefixes     = ["10.0.1.0/24"]
}

# AKS cluster
resource "azurerm_kubernetes_cluster" "main" {
  name                = var.cluster_name
  location            = data.azurerm_resource_group.main.location
  resource_group_name = data.azurerm_resource_group.main.name
  dns_prefix          = var.cluster_name
  
  default_node_pool {
    name                = "default"
    node_count          = 2
    vm_size             = "Standard_D2s_v3"
    vnet_subnet_id      = azurerm_subnet.aks.id
    enable_auto_scaling = true
    min_count           = 1
    max_count           = 5
  }
  
  identity {
    type = "SystemAssigned"
  }
  
  network_profile {
    network_plugin = "azure"
    network_policy = "calico"
  }
  
  oms_agent {
    log_analytics_workspace_id = azurerm_log_analytics_workspace.main.id
  }
  
  tags = {
    Environment = "Production"
    Project     = "CertifyEdge"
  }
}

# GPU node pool
resource "azurerm_kubernetes_cluster_node_pool" "gpu" {
  name                  = var.gpu_node_pool_name
  kubernetes_cluster_id = azurerm_kubernetes_cluster.main.id
  vm_size               = "Standard_NC24rs_v3" # A100 GPU
  node_count            = 0
  enable_auto_scaling   = true
  min_count             = 0
  max_count             = var.max_gpu_nodes
  
  node_taints = [
    "nvidia.com/gpu=true:NoSchedule"
  ]
  
  node_labels = {
    "accelerator" = "nvidia-a100"
    "spot"        = "true"
  }
  
  tags = {
    Environment = "Production"
    Project     = "CertifyEdge"
    GPU         = "A100"
  }
}

# Log Analytics workspace
resource "azurerm_log_analytics_workspace" "main" {
  name                = "${var.cluster_name}-logs"
  location            = data.azurerm_resource_group.main.location
  resource_group_name = data.azurerm_resource_group.main.name
  sku                 = "PerGB2018"
  retention_in_days   = 30
}

# Container Registry
resource "azurerm_container_registry" "main" {
  name                = "certifyedgeacr"
  resource_group_name = data.azurerm_resource_group.main.name
  location            = data.azurerm_resource_group.main.location
  sku                 = "Premium"
  admin_enabled       = true
}

# Budget alert
resource "azurerm_consumption_budget_resource_group" "main" {
  name              = "certifyedge-gpu-budget"
  resource_group_id = data.azurerm_resource_group.main.id
  
  amount     = var.budget_limit
  time_grain = "Monthly"
  
  time_period {
    start_date = "2025-01-01T00:00:00Z"
    end_date   = "2025-12-31T23:59:59Z"
  }
  
  notification {
    enabled        = true
    threshold      = 90.0
    operator       = "GreaterThan"
    contact_emails = ["admin@certifyedge.com"]
  }
  
  notification {
    enabled        = true
    threshold      = 100.0
    operator       = "GreaterThan"
    contact_emails = ["admin@certifyedge.com"]
  }
}

# Kubernetes provider
provider "kubernetes" {
  host                   = azurerm_kubernetes_cluster.main.kube_config.0.host
  username               = azurerm_kubernetes_cluster.main.kube_config.0.username
  password               = azurerm_kubernetes_cluster.main.kube_config.0.password
  client_certificate     = base64decode(azurerm_kubernetes_cluster.main.kube_config.0.client_certificate)
  client_key             = base64decode(azurerm_kubernetes_cluster.main.kube_config.0.client_key)
  cluster_ca_certificate = base64decode(azurerm_kubernetes_cluster.main.kube_config.0.cluster_ca_certificate)
}

# Helm provider
provider "helm" {
  kubernetes {
    host                   = azurerm_kubernetes_cluster.main.kube_config.0.host
    username               = azurerm_kubernetes_cluster.main.kube_config.0.username
    password               = azurerm_kubernetes_cluster.main.kube_config.0.password
    client_certificate     = base64decode(azurerm_kubernetes_cluster.main.kube_config.0.client_certificate)
    client_key             = base64decode(azurerm_kubernetes_cluster.main.kube_config.0.client_key)
    cluster_ca_certificate = base64decode(azurerm_kubernetes_cluster.main.kube_config.0.cluster_ca_certificate)
  }
}

# Karpenter for autoscaling
resource "helm_release" "karpenter" {
  name       = "karpenter"
  repository = "https://charts.karpenter.sh"
  chart      = "karpenter"
  version    = "0.32.0"
  namespace  = "karpenter"
  create_namespace = true
  
  set {
    name  = "serviceAccount.annotations.azure\\.com/role-assignment-id"
    value = azurerm_role_assignment.karpenter.id
  }
  
  set {
    name  = "clusterName"
    value = var.cluster_name
  }
  
  set {
    name  = "clusterEndpoint"
    value = azurerm_kubernetes_cluster.main.kube_config.0.host
  }
}

# Karpenter provisioner
resource "kubernetes_manifest" "karpenter_provisioner" {
  manifest = {
    apiVersion = "karpenter.sh/v1alpha5"
    kind       = "Provisioner"
    metadata = {
      name = "gpu-provisioner"
    }
    spec = {
      requirements = [
        {
          key   = "kubernetes.azure.com/scalesetpriority"
          operator = "In"
          values = ["spot"]
        },
        {
          key   = "node.kubernetes.io/instance-type"
          operator = "In"
          values = ["Standard_NC24rs_v3", "Standard_NC8rs_v3"]
        },
        {
          key   = "accelerator"
          operator = "In"
          values = ["nvidia-a100", "nvidia-a10"]
        }
      ]
      limits = {
        resources = {
          cpu    = "100"
          memory = "1000Gi"
        }
      }
      ttlSecondsAfterEmpty = 300
      ttlSecondsUntilExpired = 2592000
    }
  }
}

# GPU operator for NVIDIA drivers
resource "helm_release" "gpu_operator" {
  name       = "gpu-operator"
  repository = "https://helm.ngc.nvidia.com/nvidia"
  chart      = "gpu-operator"
  version    = "23.9.2"
  namespace  = "gpu-operator"
  create_namespace = true
  
  set {
    name  = "nvidia-device-plugin.enabled"
    value = "true"
  }
  
  set {
    name  = "nvidia-dcgm.enabled"
    value = "true"
  }
  
  set {
    name  = "nvidia-dcgm-exporter.enabled"
    value = "true"
  }
}

# Prometheus for monitoring
resource "helm_release" "prometheus" {
  name       = "prometheus"
  repository = "https://prometheus-community.github.io/helm-charts"
  chart      = "kube-prometheus-stack"
  version    = "55.0.0"
  namespace  = "monitoring"
  create_namespace = true
  
  set {
    name  = "grafana.enabled"
    value = "true"
  }
  
  set {
    name  = "alertmanager.enabled"
    value = "true"
  }
}

# Chaos Mesh for chaos engineering
resource "helm_release" "chaos_mesh" {
  name       = "chaos-mesh"
  repository = "https://charts.chaos-mesh.org"
  chart      = "chaos-mesh"
  version    = "2.6.0"
  namespace  = "chaos-testing"
  create_namespace = true
  
  set {
    name  = "dashboard.enabled"
    value = "true"
  }
  
  set {
    name  = "dashboard.persistentVolume.enabled"
    value = "true"
  }
}

# Role assignment for Karpenter
resource "azurerm_role_assignment" "karpenter" {
  scope                = data.azurerm_resource_group.main.id
  role_definition_name = "Contributor"
  principal_id         = azurerm_kubernetes_cluster.main.kubelet_identity.0.object_id
}

# Storage class for node-local SSD
resource "kubernetes_storage_class" "node_local_ssd" {
  metadata {
    name = "node-local-ssd"
  }
  
  storage_provisioner = "kubernetes.io/azure-disk"
  reclaim_policy     = "Delete"
  volume_binding_mode = "WaitForFirstConsumer"
  
  parameters = {
    skuname = "Premium_LRS"
    kind    = "Managed"
  }
}

# Namespace for GPU jobs
resource "kubernetes_namespace" "gpu_jobs" {
  metadata {
    name = "gpu-jobs"
    
    labels = {
      name = "gpu-jobs"
    }
  }
}

# ConfigMap for GPU farm configuration
resource "kubernetes_config_map" "gpu_farm_config" {
  metadata {
    name      = "gpu-farm-config"
    namespace = kubernetes_namespace.gpu_jobs.metadata.0.name
  }
  
  data = {
    "budget-limit" = var.budget_limit
    "max-gpu-nodes" = var.max_gpu_nodes
    "spot-percentage" = var.spot_instance_percentage
    "cluster-name" = var.cluster_name
    "registry-url" = azurerm_container_registry.main.login_server
  }
}

# Service account for GPU jobs
resource "kubernetes_service_account" "gpu_jobs" {
  metadata {
    name      = "gpu-jobs-sa"
    namespace = kubernetes_namespace.gpu_jobs.metadata.0.name
  }
}

# RBAC for GPU jobs
resource "kubernetes_cluster_role" "gpu_jobs" {
  metadata {
    name = "gpu-jobs-role"
  }
  
  rule {
    api_groups = [""]
    resources  = ["pods", "services"]
    verbs      = ["get", "list", "watch", "create", "update", "patch", "delete"]
  }
  
  rule {
    api_groups = ["batch"]
    resources  = ["jobs"]
    verbs      = ["get", "list", "watch", "create", "update", "patch", "delete"]
  }
}

resource "kubernetes_cluster_role_binding" "gpu_jobs" {
  metadata {
    name = "gpu-jobs-role-binding"
  }
  
  role_ref {
    api_group = "rbac.authorization.k8s.io"
    kind      = "ClusterRole"
    name      = kubernetes_cluster_role.gpu_jobs.metadata.0.name
  }
  
  subject {
    kind      = "ServiceAccount"
    name      = kubernetes_service_account.gpu_jobs.metadata.0.name
    namespace = kubernetes_namespace.gpu_jobs.metadata.0.name
  }
}

# Outputs
output "cluster_name" {
  value = azurerm_kubernetes_cluster.main.name
}

output "cluster_endpoint" {
  value = azurerm_kubernetes_cluster.main.kube_config.0.host
}

output "resource_group_name" {
  value = data.azurerm_resource_group.main.name
}

output "container_registry_url" {
  value = azurerm_container_registry.main.login_server
}

output "log_analytics_workspace_id" {
  value = azurerm_log_analytics_workspace.main.id
} 