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
    
    @lru_cache(maxsize=4)
    def get_prover_path(self, prover_name: str) -> Optional[str]:
        """
        获取prover路径（带缓存）
        
        Args:
            prover_name: Prover名称（'z3' 或 'cvc5'）
        
        Returns:
            Prover路径或None
        """
        import shutil
        
        if prover_name not in self._prover_paths:
            path = shutil.which(prover_name)
            self._prover_paths[prover_name] = path
        
        return self._prover_paths[prover_name]
    
    def clear(self):
        """清空缓存"""
        self._prover_paths.clear()
        self.get_prover_path.cache_clear()

