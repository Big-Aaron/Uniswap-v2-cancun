// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {MockERC20} from "forge-std/mocks/MockERC20.sol";

contract ERC20Token is MockERC20 {
    constructor(string memory name_, string memory symbol_, uint8 decimals_) {
        initialize(name_, symbol_, decimals_);
    }

    function mint(address to, uint256 amount) public {
        _mint(to, amount);
    }
}
