// SPDX-License-Identifier: AGPL-3.0-or-later
pragma solidity ^0.8.28;

contract DaiNoop {
    function checkPermit(address, address, uint256, uint256, bool, uint8, bytes32, bytes32) external pure returns (bool) { return true; }
}

contract DaiMocked {
    mapping(address => uint256) public wards;
    uint256 public totalSupply;
    mapping(address => uint256) public balanceOf;
    mapping(address => mapping(address => uint256)) public allowance;
    mapping(address => uint256) public nonces;
    DaiNoop public mock;
    uint8 public constant decimals = 18;

    modifier auth() { require(wards[msg.sender] == 1); _; }
    constructor(uint256, address mock_) { wards[msg.sender] = 1; mock = DaiNoop(mock_); }
    function rely(address usr) external auth { wards[usr] = 1; }
    function deny(address usr) external auth { wards[usr] = 0; }

    function approve(address usr, uint256 wad) external returns (bool) { allowance[msg.sender][usr] = wad; return true; }
    function transfer(address dst, uint256 wad) external returns (bool) { _move(msg.sender, dst, wad); return true; }
    function transferFrom(address src, address dst, uint256 wad) external returns (bool) {
        if (src != msg.sender) allowance[src][msg.sender] -= wad;
        _move(src, dst, wad);
        return true;
    }
    function _move(address src, address dst, uint256 wad) internal {
        require(balanceOf[src] >= wad);
        if (src != dst) { balanceOf[src] -= wad; balanceOf[dst] += wad; }
    }
    function mint(address usr, uint256 wad) external auth { balanceOf[usr] += wad; totalSupply += wad; }
    function burn(address usr, uint256 wad) external { require(usr == msg.sender); balanceOf[usr] -= wad; totalSupply -= wad; }

    function permit(address holder, address spender, uint256 nonce, uint256 expiry, bool allowed, uint8 v, bytes32 r, bytes32 s) external {
        require(holder != address(0));
        require(mock.checkPermit(holder, spender, nonce, expiry, allowed, v, r, s));
        require(nonce == nonces[holder]);
        nonces[holder] += 1;
        allowance[holder][spender] = allowed ? type(uint256).max : 0;
    }
}
