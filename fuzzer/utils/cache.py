#!/usr/bin/env python3
"""
缓存工具
减少重复操作，提高性能
"""

from functools import lru_cache
from typing import Dict, Optional
import hashlib
import json


class FileCache:
    """文件缓存类"""
    
    def __init__(self, max_size: int = 128):
        """
        初始化文件缓存
        
        Args:
            max_size: 最大缓存大小（LRU缓存项数）
        """
        self.max_size = max_size
        self._cache: Dict[str, bytes] = {}
    
    def _get_key(self, filepath: str) -> str:
        """生成缓存键"""
        return hashlib.md5(filepath.encode()).hexdigest()
    
    def get(self, filepath: str) -> Optional[bytes]:
        """
        获取缓存的文件内容
        
        Args:
            filepath: 文件路径
        
        Returns:
            文件内容（字节）或None
        """
        key = self._get_key(filepath)
        return self._cache.get(key)
    
    def set(self, filepath: str, content: bytes):
        """
        设置缓存
        
        Args:
            filepath: 文件路径
            content: 文件内容
        """
        key = self._get_key(filepath)
        
        # 如果超过最大大小，删除最旧的项
        if len(self._cache) >= self.max_size:
            # 删除第一个项（LRU）
            first_key = next(iter(self._cache))
            del self._cache[first_key]
        
        self._cache[key] = content
    
    def clear(self):
        """清空缓存"""
        self._cache.clear()
    
    def size(self) -> int:
        """返回缓存大小"""
        return len(self._cache)


class ProverPathCache:
    """Prover路径缓存"""
    
    def __init__(self):
        """初始化路径缓存"""
        self._prover_paths: Dict[str, Optional[str]] = {}
        
        # 支持的prover及其可能的命令名称
        self.prover_commands = {
            'z3': ['z3'],
            'cvc5': ['cvc5'],
            'eprover': ['eprover', 'eprover-ho'],
            'vampire': ['vampire', 'vampire_mac'],
            'spass': ['spass'],
        }
    
    @lru_cache(maxsize=10)
    def get_prover_path(self, prover_name: str) -> Optional[str]:
        """
        获取prover路径（带缓存）
        
        Args:
            prover_name: Prover名称（'z3', 'cvc5', 'eprover', 'vampire', 'spass'）
        
        Returns:
            Prover路径或None
        """
        import shutil
        
        if prover_name in self._prover_paths:
            return self._prover_paths[prover_name]
        
        # 检查prover是否在支持列表中
        if prover_name not in self.prover_commands:
            return None
        
        # 尝试每个可能的命令名称
        for cmd in self.prover_commands[prover_name]:
            path = shutil.which(cmd)
            if path:
                self._prover_paths[prover_name] = path
                return path
        
        # 如果没有找到，缓存None
        self._prover_paths[prover_name] = None
        return None
    
    def list_available_provers(self) -> list:
        """
        列出所有可用的prover
        
        Returns:
            可用prover名称列表
        """
        available = []
        for prover_name in self.prover_commands.keys():
            if self.get_prover_path(prover_name):
                available.append(prover_name)
        return available
    
    def clear(self):
        """清空缓存"""
        self._prover_paths.clear()
        self.get_prover_path.cache_clear()

