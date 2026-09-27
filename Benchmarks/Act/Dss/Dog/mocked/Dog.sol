// SPDX-License-Identifier: AGPL-3.0-or-later
pragma solidity ^0.8.28;

contract DogNoop {
    function clipIlk() external pure returns (bytes32) { return bytes32(0); }
    function grab(bytes32, address, address, address, int256, int256) external {}
    function fess(uint256) external {}
    function kick(uint256, uint256, address, address) external pure returns (uint256) { return 1; }
}

contract DogMocked {
    mapping(address => uint256) public wards;
    mapping(bytes32 => address) public ilkClip;
    mapping(bytes32 => uint256) public ilkChop;
    mapping(bytes32 => uint256) public ilkHole;
    mapping(bytes32 => uint256) public ilkDirt;
    uint256 public live;
    uint256 public Hole;
    uint256 public Dirt;
    address public vow;
    DogNoop public mock;

    uint256 internal constant WAD = 10 ** 18;
    modifier auth() { require(wards[msg.sender] == 1); _; }
    constructor(address mock_) { wards[msg.sender] = 1; live = 1; mock = DogNoop(mock_); }

    function rely(address usr) external auth { wards[usr] = 1; }
    function deny(address usr) external auth { wards[usr] = 0; }
    function fileHole(uint256 data) external auth { Hole = data; }
    function fileVow(address data) external auth { vow = data; }
    function fileIlk(bytes32 ilk, uint256 chop, uint256 hole) external auth { require(chop >= WAD); ilkChop[ilk] = chop; ilkHole[ilk] = hole; }
    function fileClip(bytes32 ilk, address clip) external auth { require(mock.clipIlk() == ilk); ilkClip[ilk] = clip; }
    function chop(bytes32 ilk) external view returns (uint256) { return ilkChop[ilk]; }
    function digs(bytes32 ilk, uint256 rad) external auth { Dirt -= rad; ilkDirt[ilk] -= rad; }
    function cage() external auth { live = 0; }

    function bark(bytes32 ilk, address urn, address kpr) external returns (uint256 id) {
        require(live == 1 && ilkChop[ilk] >= WAD);
        require(Hole > Dirt && ilkHole[ilk] > ilkDirt[ilk]);
        mock.grab(ilk, urn, ilkClip[ilk], vow, -int256(1), -int256(1));
        mock.fess(1);
        Dirt += 1;
        ilkDirt[ilk] += 1;
        id = mock.kick(1, 1, urn, kpr);
    }
}
