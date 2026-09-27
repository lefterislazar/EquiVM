// SPDX-License-Identifier: GPL-3.0-or-later
pragma solidity ^0.8.28;

contract WETH9NoopPayee {
    function pay() external payable {}
}

contract WETH9Mocked {
    uint8 public constant decimals = 18;
    mapping(address => uint256) public balanceOf;
    mapping(address => mapping(address => uint256)) public allowance;
    WETH9NoopPayee public mock;

    constructor(address mock_) { mock = WETH9NoopPayee(mock_); }

    function deposit() external payable { balanceOf[msg.sender] += msg.value; }

    function withdraw(uint256 wad) external {
        balanceOf[msg.sender] -= wad;
        mock.pay{value: wad}();
    }

    function totalSupply() external view returns (uint256) { return address(this).balance; }

    function approve(address guy, uint256 wad) external returns (bool) {
        allowance[msg.sender][guy] = wad;
        return true;
    }

    function transfer(address dst, uint256 wad) external returns (bool) {
        return transferFrom(msg.sender, dst, wad);
    }

    function transferFrom(address src, address dst, uint256 wad) public returns (bool) {
        require(balanceOf[src] >= wad);
        if (src != msg.sender && allowance[src][msg.sender] != type(uint256).max) {
            allowance[src][msg.sender] -= wad;
        }
        if (src != dst) {
            balanceOf[src] -= wad;
            balanceOf[dst] += wad;
        }
        return true;
    }
}
