// SPDX-License-Identifier: AGPL-3.0-or-later
pragma solidity ^0.8.28;

contract EndNoop {
    function cageAll() external {}
    function readArt(bytes32) external pure returns (uint256) { return 1; }
    function readInk(bytes32, address) external pure returns (uint256) { return 1; }
    function readDebt() external pure returns (uint256) { return 1; }
    function readDai(address) external pure returns (uint256) { return 0; }
    function readCure() external pure returns (uint256) { return 0; }
    function grab(bytes32, address, address, address, int256, int256) external {}
    function move(address, address, uint256) external {}
    function flux(bytes32, address, address, uint256) external {}
    function suck(address, address, uint256) external {}
    function yank(uint256) external {}
}

contract EndMocked {
    mapping(address => uint256) public wards;
    uint256 public live;
    uint256 public debt;
    mapping(bytes32 => uint256) public tag;
    mapping(bytes32 => uint256) public gap;
    mapping(bytes32 => uint256) public Art;
    mapping(bytes32 => uint256) public fix;
    mapping(address => uint256) public bag;
    mapping(bytes32 => mapping(address => uint256)) public out;
    EndNoop public mock;
    modifier auth() { require(wards[msg.sender] == 1); _; }
    constructor(address mock_) { wards[msg.sender] = 1; live = 1; mock = EndNoop(mock_); }
    function rely(address usr) external auth { wards[usr] = 1; }
    function deny(address usr) external auth { wards[usr] = 0; }
    function cage() external auth { require(live == 1); live = 0; mock.cageAll(); }
    function cageIlk(bytes32 ilk) external { require(live == 0 && tag[ilk] == 0); Art[ilk] = mock.readArt(ilk); tag[ilk] = 1; }
    function snip(bytes32 ilk, uint256 id) external { require(tag[ilk] != 0); mock.suck(address(this), address(this), 1); mock.yank(id); mock.grab(ilk, msg.sender, address(this), address(this), 1, 1); Art[ilk] += 1; }
    function skip(bytes32 ilk, uint256 id) external { require(tag[ilk] != 0); mock.suck(address(this), address(this), 1); mock.yank(id); mock.grab(ilk, msg.sender, address(this), address(this), 1, 1); Art[ilk] += 1; }
    function skim(bytes32 ilk, address urn) external { require(tag[ilk] != 0); uint256 ink = mock.readInk(ilk, urn); gap[ilk] += ink; mock.grab(ilk, urn, address(this), address(this), -int256(ink), 0); }
    function free(bytes32 ilk) external { require(live == 0); uint256 ink = mock.readInk(ilk, msg.sender); mock.grab(ilk, msg.sender, msg.sender, address(this), -int256(ink), 0); }
    function thaw() external { require(live == 0 && debt == 0 && mock.readDai(address(this)) == 0); debt = mock.readDebt() - mock.readCure(); }
    function flow(bytes32 ilk) external { require(debt != 0 && fix[ilk] == 0); fix[ilk] = 1; }
    function pack(uint256 wad) external { require(debt != 0); mock.move(msg.sender, address(this), wad); bag[msg.sender] += wad; }
    function cash(bytes32 ilk, uint256 wad) external { require(fix[ilk] != 0); mock.flux(ilk, address(this), msg.sender, wad); out[ilk][msg.sender] += wad; require(out[ilk][msg.sender] <= bag[msg.sender]); }
}
