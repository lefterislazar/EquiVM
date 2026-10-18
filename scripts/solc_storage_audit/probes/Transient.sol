// SPDX-License-Identifier: UNLICENSED
// @min 0.8.28
pragma solidity >=0.8.28;

contract Transient {
  uint256 transient t; uint8 transient t8; int8 transient ti8; bool transient tb; address transient ta;

  function w_t(uint256 x) external { t = x; }
  function r_t() external view returns (uint256) { return t; }
  function d_t() external { delete t; }
  function w_t8(uint8 x) external { t8 = x; }
  function r_t8() external view returns (uint8) { return t8; }
  function d_t8() external { delete t8; }
  function w_ti8(int8 x) external { ti8 = x; }
  function r_ti8() external view returns (int8) { return ti8; }
  function w_tb(bool x) external { tb = x; }
  function w_ta(address x) external { ta = x; }
  function d_ta() external { delete ta; }
}
