// SPDX-License-Identifier: AGPL-3.0-or-later
pragma solidity ^0.8.28;

contract VowNoop {
    function hope(address) external {}
    function nope(address) external {}
    function dai(address) external pure returns (uint256) { return 0; }
    function sin(address) external pure returns (uint256) { return 0; }
    function heal(uint256) external {}
    function kickFlop(address, uint256, uint256) external pure returns (uint256) { return 1; }
    function kickFlap(uint256, uint256) external pure returns (uint256) { return 1; }
    function cageFlap(uint256) external {}
    function cageFlop() external {}
}

contract VowMocked {
    mapping(address => uint256) public wards;
    uint256 public Sin;
    uint256 public Ash;
    uint256 public wait;
    uint256 public dump;
    uint256 public sump;
    uint256 public bump;
    uint256 public hump;
    uint256 public live;
    VowNoop public mock;

    modifier auth() { require(wards[msg.sender] == 1); _; }

    constructor(address mock_) {
        wards[msg.sender] = 1;
        mock = VowNoop(mock_);
        mock.hope(address(this));
        live = 1;
    }

    function rely(address usr) external auth { require(live == 1); wards[usr] = 1; }
    function deny(address usr) external auth { wards[usr] = 0; }
    function fileWait(uint256 value) external auth { wait = value; }
    function fileDump(uint256 value) external auth { dump = value; }
    function fileSump(uint256 value) external auth { sump = value; }
    function fileBump(uint256 value) external auth { bump = value; }
    function fileHump(uint256 value) external auth { hump = value; }

    function heal(uint256 rad) external {
        require(rad <= mock.dai(address(this)));
        require(rad <= mock.sin(address(this)) - Sin - Ash);
        mock.heal(rad);
    }

    function kiss(uint256 rad) external {
        require(rad <= Ash && rad <= mock.dai(address(this)));
        Ash -= rad;
        mock.heal(rad);
    }

    function flop() external returns (uint256 id) {
        require(sump <= mock.sin(address(this)) - Sin - Ash);
        require(mock.dai(address(this)) == 0);
        Ash += sump;
        id = mock.kickFlop(address(this), dump, sump);
    }

    function flap() external returns (uint256 id) {
        require(mock.dai(address(this)) >= mock.sin(address(this)) + bump + hump);
        require(mock.sin(address(this)) - Sin - Ash == 0);
        id = mock.kickFlap(bump, 0);
    }

    function cage() external auth {
        require(live == 1);
        live = 0;
        Sin = 0;
        Ash = 0;
        mock.cageFlap(mock.dai(address(this)));
        mock.cageFlop();
        mock.heal(0);
    }
}
