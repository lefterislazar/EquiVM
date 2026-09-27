// SPDX-License-Identifier: AGPL-3.0-or-later
pragma solidity ^0.8.28;

contract JugNoop {
    function readRate(bytes32) external pure returns (uint256) { return 10 ** 27; }
    function fold(bytes32, address, int256) external {}
}

contract JugMocked {
    mapping(address => uint256) public wards;
    mapping(bytes32 => uint256) public duty;
    mapping(bytes32 => uint256) public rho;
    uint256 public base;
    address public vow;
    JugNoop public mock;

    uint256 internal constant ONE = 10 ** 27;

    modifier auth() { require(wards[msg.sender] == 1); _; }

    constructor(address mock_) {
        wards[msg.sender] = 1;
        mock = JugNoop(mock_);
    }

    function rely(address usr) external auth { wards[usr] = 1; }
    function deny(address usr) external auth { wards[usr] = 0; }
    function fileBase(uint256 value) external auth { base = value; }
    function fileVow(address value) external auth { vow = value; }

    function init(bytes32 ilk) external auth {
        require(duty[ilk] == 0);
        duty[ilk] = ONE;
    }

    function fileDuty(bytes32 ilk, uint256 value) external auth {
        require(duty[ilk] != 0);
        duty[ilk] = value;
    }

    function drip(bytes32 ilk) external returns (uint256 rate) {
        rate = mock.readRate(ilk);
        mock.fold(ilk, vow, 0);
        rho[ilk] += 1;
    }
}
