"""
Oracle模块
"""

from .crash_oracle import CrashOracle, ProverResult as CrashProverResult, OracleResult
from .differential_oracle import DifferentialOracle, DifferentialResult, ProverStatus
from .reconstruction_oracle import (
    ReconstructionOracle, 
    ReconstructionResult,
    ReconstructionStatus,
    FailureType,
    ProverResult as ReconstructionProverResult
)

__all__ = [
    'CrashOracle', 'CrashProverResult', 'OracleResult',
    'DifferentialOracle', 'DifferentialResult', 'ProverStatus',
    'ReconstructionOracle', 'ReconstructionResult', 'ReconstructionStatus', 'FailureType', 'ReconstructionProverResult'
]

