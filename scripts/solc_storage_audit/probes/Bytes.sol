// SPDX-License-Identifier: UNLICENSED
pragma solidity >=0.8.0;

contract Bytes {
  bytes b; bytes b2; string s; string s2;

  // Setters for the sources of storage-to-storage copies (not analyzed).
  function set_b2(bytes memory x) external { b2 = x; }
  function set_s2(string memory x) external { s2 = x; }

  function w_b_mem(bytes memory x) external { b = x; }
  function w_b_cd(bytes calldata x) external { b = x; }
  function w_b_sto() external { b = b2; }
  function w_b_lit() external { b = "short literal"; }
  function w_b_litlong() external { b = "a literal that is definitely longer than thirty-two bytes"; }
  function w_b_froms() external { b = bytes(s); }
  function r_b() external view returns (bytes memory) { return b; }
  function d_b() external { delete b; }
  function len_b() external view returns (uint256) { return b.length; }
  function push0_b() external { b.push(); }
  function pushv_b(bytes1 x) external { b.push(x); }
  function pop_b() external { b.pop(); }
  function wi_b(uint256 i, bytes1 v) external { b[i] = v; }
  function ri_b(uint256 i) external view returns (bytes1) { return b[i]; }
  function di_b(uint256 i) external { delete b[i]; }
  function w_s_mem(string memory x) external { s = x; }
  function w_s_cd(string calldata x) external { s = x; }
  function w_s_sto() external { s = s2; }
  function r_s() external view returns (string memory) { return s; }
  function d_s() external { delete s; }
  function len_s() external view returns (uint256) { return bytes(s).length; }
  function pushv_s(bytes1 x) external { bytes(s).push(x); }
  function pop_s() external { bytes(s).pop(); }
}
