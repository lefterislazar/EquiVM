// SPDX-License-Identifier: UNLICENSED
pragma solidity >=0.8.0;

interface I { function f() external; }

contract ValueTypes {
  enum E { A, B, C }
  uint8 u8; int8 i8; bool bo; address ad; bytes7 b7; E en; I ct; uint40 u40; int24 i24;
  function() external fx;
  function() internal fi;
  uint256 u256; int256 i256; bytes32 b32;

  function helper() internal {}

  function w_u8(uint8 x) external { u8 = x; }
  function r_u8() external view returns (uint8) { return u8; }
  function d_u8() external { delete u8; }
  function w_i8(int8 x) external { i8 = x; }
  function r_i8() external view returns (int8) { return i8; }
  function d_i8() external { delete i8; }
  function w_bo(bool x) external { bo = x; }
  function r_bo() external view returns (bool) { return bo; }
  function d_bo() external { delete bo; }
  function w_ad(address x) external { ad = x; }
  function r_ad() external view returns (address) { return ad; }
  function d_ad() external { delete ad; }
  function w_b7(bytes7 x) external { b7 = x; }
  function r_b7() external view returns (bytes7) { return b7; }
  function d_b7() external { delete b7; }
  function w_en(E x) external { en = x; }
  function r_en() external view returns (E) { return en; }
  function d_en() external { delete en; }
  function w_ct(I x) external { ct = x; }
  function r_ct() external view returns (I) { return ct; }
  function d_ct() external { delete ct; }
  function w_u40(uint40 x) external { u40 = x; }
  function r_u40() external view returns (uint40) { return u40; }
  function d_u40() external { delete u40; }
  function w_i24(int24 x) external { i24 = x; }
  function r_i24() external view returns (int24) { return i24; }
  function d_i24() external { delete i24; }
  function w_fx(function() external x) external { fx = x; }
  function r_fx() external view returns (function() external) { return fx; }
  function d_fx() external { delete fx; }
  function w_fi() external { fi = helper; }
  function d_fi() external { delete fi; }
  function w_u256(uint256 x) external { u256 = x; }
  function r_u256() external view returns (uint256) { return u256; }
  function d_u256() external { delete u256; }
  function w_i256(int256 x) external { i256 = x; }
  function r_i256() external view returns (int256) { return i256; }
  function d_i256() external { delete i256; }
  function w_b32(bytes32 x) external { b32 = x; }
  function r_b32() external view returns (bytes32) { return b32; }
  function d_b32() external { delete b32; }
  function rmw_u8(uint8 x) external { u8 += x; }
  function rmw_i24(int24 x) external { i24 -= x; }
}
