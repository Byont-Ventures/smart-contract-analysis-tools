// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.13;
pragma abicoder v2;

import "@openzeppelin/contracts/token/ERC20/ERC20.sol";
import "@smart-contracts/interfaces/IVeriToken.sol";

contract VeriToken is ERC20, IVeriToken {
    constructor() ERC20("VeriToken", "VT") {}

    // Change it from the default 18 to 6
    function decimals() public view override returns (uint8) {
        return 6;
    }

    function mint(uint256 amount) external override {
        _mint(msg.sender, amount);
    }

    function burn(uint256 amount) external override {
        _burn(msg.sender, amount);
    }
}
