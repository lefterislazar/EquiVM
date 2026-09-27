// SPDX-License-Identifier: AGPL-3.0-or-later
pragma solidity ^0.8.28;

contract CatNoop {
    function nope(address) external {}
    function hope(address) external {}
    function grab(bytes32, address, address, address, int256, int256) external {}
    function fess(uint256) external {}
    function kick(address, address, uint256, uint256, uint256) external pure returns (uint256) { return 1; }
}

contract CatMocked {
    mapping(address => uint256) public wards;
    mapping(bytes32 => address) public ilkFlip;
    mapping(bytes32 => uint256) public ilkChop;
    mapping(bytes32 => uint256) public ilkDunk;
    uint256 public live;
    uint256 public box;
    uint256 public litter;
    address public vow;
    CatNoop public mock;

    uint256 internal constant RAY = 10 ** 27;
    modifier auth() { require(wards[msg.sender] == 1); _; }

    constructor(address mock_) {
        wards[msg.sender] = 1;
        live = 1;
        mock = CatNoop(mock_);
    }

    function rely(address usr) external auth { wards[usr] = 1; }
    function deny(address usr) external auth { wards[usr] = 0; }
    function fileBox(uint256 data) external auth { box = data; }
    function fileVow(address data) external auth { vow = data; }
    function fileIlk(bytes32 ilk, uint256 chop, uint256 dunk) external auth { ilkChop[ilk] = chop; ilkDunk[ilk] = dunk; }
    function fileFlip(bytes32 ilk, address flip) external auth {
        mock.nope(ilkFlip[ilk]);
        ilkFlip[ilk] = flip;
        mock.hope(flip);
    }
    function claw(uint256 rad) external auth { litter -= rad; }
    function cage() external auth { live = 0; }

    function bite(bytes32 ilk, address urn) external returns (uint256 id) {
        require(live == 1 && ilkDunk[ilk] != 0 && ilkChop[ilk] != 0);
        require(box - litter >= RAY);
        mock.grab(ilk, urn, address(this), vow, -int256(1), -int256(1));
        mock.fess(RAY);
        litter += RAY;
        id = mock.kick(urn, vow, RAY, 1, 0);
    }
}
