// SPDX-License-Identifier: AGPL-3.0-or-later
pragma solidity ^0.8.28;

contract FlipperNoop {
    function flux(bytes32, address, address, uint256) external {}
    function move(address, address, uint256) external {}
    function claw(uint256) external {}
}

contract FlipperMocked {
    mapping(address => uint256) public wards;
    mapping(uint256 => uint256) public bid;
    mapping(uint256 => uint256) public lot;
    mapping(uint256 => uint256) public tab;
    mapping(uint256 => address) public guy;
    uint256 public kicks;
    bytes32 public ilk;
    FlipperNoop public mock;
    modifier auth() { require(wards[msg.sender] == 1); _; }
    constructor(address mock_, bytes32 ilk_) { wards[msg.sender] = 1; mock = FlipperNoop(mock_); ilk = ilk_; }
    function rely(address usr) external auth { wards[usr] = 1; }
    function deny(address usr) external auth { wards[usr] = 0; }
    function kick(address, address, uint256, uint256 lot_, uint256) external auth returns (uint256 id) { id = ++kicks; mock.flux(ilk, msg.sender, address(this), lot_); }
    function yank(uint256 id) external auth { require(guy[id] != address(0) && bid[id] < tab[id]); mock.claw(tab[id]); mock.flux(ilk, address(this), msg.sender, lot[id]); mock.move(msg.sender, guy[id], bid[id]); }
}
