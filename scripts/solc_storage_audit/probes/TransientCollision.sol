// SPDX-License-Identifier: UNLICENSED
// @min 0.8.28
// @nosplit
pragma solidity >=0.8.28;

// Both deletes must stay in one contract: the bug is a helper name shared by the two.
contract TransientCollision {
  uint256 p; uint256 transient t;

  function d_p() external { delete p; }
  function d_t() external { delete t; }
  function w_both(uint256 x) external { p = x; t = x; }
  function r_both() external view returns (uint256, uint256) { return (p, t); }
}
