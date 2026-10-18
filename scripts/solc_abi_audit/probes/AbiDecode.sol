// SPDX-License-Identifier: UNLICENSED
pragma solidity >=0.8.13;

// `abi.decode` of memory and calldata byte arrays.
contract AbiDecode {
  struct S { uint8 a; bytes b; uint16[] c; }

  function dU8(bytes memory d) external pure returns (uint8) { return abi.decode(d, (uint8)); }
  function dBo(bytes memory d) external pure returns (bool) { return abi.decode(d, (bool)); }
  function dArr(bytes memory d) external pure returns (uint8[] memory) { return abi.decode(d, (uint8[])); }
  function dNN(bytes memory d) external pure returns (uint8[][] memory) { return abi.decode(d, (uint8[][])); }
  function dBy(bytes memory d) external pure returns (bytes memory) { return abi.decode(d, (bytes)); }
  function dS(bytes memory d) external pure returns (S memory) { return abi.decode(d, (S)); }
  function dMix(bytes memory d) external pure returns (uint8, bytes memory) { return abi.decode(d, (uint8, bytes)); }
  function dCd(bytes calldata d) external pure returns (uint8[] memory) { return abi.decode(d, (uint8[])); }
  function dCdNN(bytes calldata d) external pure returns (uint8[][] memory) { return abi.decode(d, (uint8[][])); }
}
