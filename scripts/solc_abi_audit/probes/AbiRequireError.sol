// SPDX-License-Identifier: UNLICENSED
// @min 0.8.26
pragma solidity >=0.8.26;

// `require` with a custom error, positional and with named arguments out of order
// (MisorderedNamedParametersInRequireWithCustomErrors, via-IR, fixed in 0.8.37).
contract AbiRequireError {
  error Err(uint8 a, bytes b);

  function reqPos(bool c, uint8 a, bytes memory b) external pure { require(c, Err(a, b)); }
  function reqNamed(bool c, uint8 a, bytes memory b) external pure { require(c, Err({b: b, a: a})); }
}
