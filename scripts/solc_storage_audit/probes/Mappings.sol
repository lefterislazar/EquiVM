// SPDX-License-Identifier: UNLICENSED
pragma solidity >=0.8.0;

contract Mappings {
  struct S { uint8 a; uint128 b; uint256 c; }
  mapping(uint256 => uint256) mu;
  mapping(address => uint8) ma;
  mapping(int8 => uint256) mi8;
  mapping(bytes4 => uint256) mb4;
  mapping(bool => uint256) mbo;
  mapping(bytes => uint256) mb;
  mapping(string => uint256) mst;
  mapping(uint256 => S) mS;
  mapping(uint256 => mapping(uint256 => uint256)) mm;
  mapping(uint256 => bytes) mby;
  mapping(uint256 => uint256[]) mda;

  function w_mu(uint256 k, uint256 v) external { mu[k] = v; }
  function r_mu(uint256 k) external view returns (uint256) { return mu[k]; }
  function d_mu(uint256 k) external { delete mu[k]; }
  function w_ma(address k, uint8 v) external { ma[k] = v; }
  function r_ma(address k) external view returns (uint8) { return ma[k]; }
  function w_mi8(int8 k, uint256 v) external { mi8[k] = v; }
  function r_mi8(int8 k) external view returns (uint256) { return mi8[k]; }
  function w_mb4(bytes4 k, uint256 v) external { mb4[k] = v; }
  function w_mbo(bool k, uint256 v) external { mbo[k] = v; }
  function w_mb_cd(bytes calldata k, uint256 v) external { mb[k] = v; }
  function w_mb_mem(bytes memory k, uint256 v) external { mb[k] = v; }
  function r_mb(bytes calldata k) external view returns (uint256) { return mb[k]; }
  function w_mst(string calldata k, uint256 v) external { mst[k] = v; }
  function w_mS(uint256 k, S memory v) external { mS[k] = v; }
  function d_mS(uint256 k) external { delete mS[k]; }
  function w_mm(uint256 k, uint256 j, uint256 v) external { mm[k][j] = v; }
  function w_mby(uint256 k, bytes memory v) external { mby[k] = v; }
  function d_mby(uint256 k) external { delete mby[k]; }
  function pushv_mda(uint256 k, uint256 v) external { mda[k].push(v); }
  function d_mda(uint256 k) external { delete mda[k]; }
}
