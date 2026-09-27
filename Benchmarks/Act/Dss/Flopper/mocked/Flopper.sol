// SPDX-License-Identifier: AGPL-3.0-or-later
pragma solidity ^0.8.28;

contract FlopperNoop {
    function suck(address, address, uint256) external {}
    function mint(address, uint256) external {}
}

contract FlopperMocked {
    mapping(address => uint256) public wards;
    mapping(uint256 => uint256) public bid;
    mapping(uint256 => uint256) public lot;
    mapping(uint256 => address) public guy;
    uint256 public kicks;
    uint256 public live;
    address public vow;
    FlopperNoop public mock;
    modifier auth() { require(wards[msg.sender] == 1); _; }
    constructor(address mock_) { wards[msg.sender] = 1; live = 1; mock = FlopperNoop(mock_); }
    function rely(address usr) external auth { wards[usr] = 1; }
    function deny(address usr) external auth { wards[usr] = 0; }
    function kick(address, uint256, uint256) external auth returns (uint256 id) { require(live == 1); id = ++kicks; }
    function deal(uint256 id) external { require(live == 1 && guy[id] != address(0)); mock.mint(guy[id], lot[id]); }
    function cage() external auth { live = 0; vow = msg.sender; }
    function yank(uint256 id) external { require(live == 0 && guy[id] != address(0)); mock.suck(vow, guy[id], bid[id]); }
}
