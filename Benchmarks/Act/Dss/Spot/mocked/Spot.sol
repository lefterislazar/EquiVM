// SPDX-License-Identifier: AGPL-3.0-or-later
pragma solidity ^0.8.28;

contract SpotNoop {
    function readValue(bytes32) external pure returns (uint256) { return 10 ** 18; }
    function readValid(bytes32) external pure returns (bool) { return true; }
    function setSpot(bytes32, uint256) external {}
}

contract SpotMocked {
    mapping(address => uint256) public wards;
    mapping(bytes32 => address) public ilkPip;
    mapping(bytes32 => uint256) public ilkMat;
    uint256 public par;
    uint256 public live;
    SpotNoop public mock;

    modifier auth() {
        require(wards[msg.sender] == 1);
        _;
    }

    constructor(address mock_) {
        wards[msg.sender] = 1;
        par = 10 ** 27;
        live = 1;
        mock = SpotNoop(mock_);
    }

    function rely(address usr) external auth { wards[usr] = 1; }
    function deny(address usr) external auth { wards[usr] = 0; }
    function filePip(bytes32 ilk, address pip) external auth { require(live == 1); ilkPip[ilk] = pip; }
    function fileMat(bytes32 ilk, uint256 mat) external auth { require(live == 1); ilkMat[ilk] = mat; }
    function filePar(uint256 par_) external auth { require(live == 1); par = par_; }
    function cage() external auth { live = 0; }

    function poke(bytes32 ilk) external {
        uint256 val = mock.readValue(ilk);
        bool valid = mock.readValid(ilk);
        mock.setSpot(ilk, valid ? val : 0);
    }
}
