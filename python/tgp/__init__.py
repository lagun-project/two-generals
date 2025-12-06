"""
Two Generals Protocol (TGP) - Pure Epistemic Implementation

A deterministically failsafe solution to the Coordinated Attack Problem
using cryptographic proof stapling and bilateral construction properties.
"""

__version__ = "0.1.0"
__author__ = "Riff Labs"
__license__ = "AGPLv3"

from .types import (
    Commitment,
    DoubleProof,
    TripleProof,
    QuadProof,
    Party,
    Message,
)
from .crypto import KeyPair, PublicKey
from .protocol import TwoGenerals, ProtocolState

__all__ = [
    "Commitment",
    "DoubleProof",
    "TripleProof",
    "QuadProof",
    "Party",
    "Message",
    "KeyPair",
    "PublicKey",
    "TwoGenerals",
    "ProtocolState",
]