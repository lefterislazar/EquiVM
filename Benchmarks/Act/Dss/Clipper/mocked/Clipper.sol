// SPDX-License-Identifier: AGPL-3.0-or-later
pragma solidity ^0.8.28;

contract ClipperNoop {
    function suck(address, address, uint256) external {}
    function flux(bytes32, address, address, uint256) external {}
    function move(address, address, uint256) external {}
    function digs(bytes32, uint256) external {}
    function callback(address, uint256, uint256) external {}
    function dust(bytes32) external pure returns (uint256) { return 10 ** 18; }
    function chop(bytes32) external pure returns (uint256) { return 10 ** 18; }
}

contract ClipperMocked {
    mapping(address => uint256) public wards;
    mapping(uint256 => uint256) public saleTab;
    mapping(uint256 => uint256) public saleLot;
    mapping(uint256 => address) public saleUsr;
    bytes32 public ilk;
    uint256 public kicks;
    uint256 public stopped;
    uint256 public chost;
    address public vow;
    ClipperNoop public mock;
    modifier auth() { require(wards[msg.sender] == 1); _; }
    constructor(address mock_, bytes32 ilk_) { wards[msg.sender] = 1; mock = ClipperNoop(mock_); ilk = ilk_; }
    function rely(address usr) external auth { wards[usr] = 1; }
    function deny(address usr) external auth { wards[usr] = 0; }
    function fileStopped(uint256 data) external auth { stopped = data; }
    function fileVow(address data) external auth { vow = data; }
    function kick(uint256 tab, uint256 lot, address usr, address kpr) external auth returns (uint256 id) { require(stopped < 1 && tab > 0 && lot > 0 && usr != address(0)); id = ++kicks; mock.suck(vow, kpr, 1); }
    function redo(uint256 id, address kpr) external { require(stopped < 2 && saleUsr[id] != address(0)); mock.suck(vow, kpr, 1); }
    function upchost() external { chost = (mock.dust(ilk) * mock.chop(ilk)) / 10 ** 18; }
    function yank(uint256 id) external auth { require(saleUsr[id] != address(0)); mock.digs(ilk, saleTab[id]); mock.flux(ilk, address(this), msg.sender, saleLot[id]); }
}
