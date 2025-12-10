"""
Isabelle接口单元测试

运行方式:
    pip install pytest pytest-cov pytest-mock
    pytest tests/test_isabelle_interface.py -v --cov=code
"""

import pytest
import tempfile
import os
from pathlib import Path
from unittest.mock import Mock, patch, MagicMock
import subprocess
import sys

# 添加code模块到路径
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'code'))

from isabelle_interface import (
    IsabelleInterface,
    IsabelleStatus,
    IsabelleResult,
    IsabelleNotFoundError,
    InvalidTheoryNameError
)


class TestIsabelleInterfaceInit:
    """初始化测试"""
    
    @patch('subprocess.run')
    def test_init_success(self, mock_run):
        """测试：成功初始化"""
        mock_result = MagicMock()
        mock_result.returncode = 0
        mock_result.stdout = "Isabelle2023"
        mock_run.return_value = mock_result
        
        interface = IsabelleInterface()
        assert interface.isabelle_path == "isabelle"
    
    def test_init_isabelle_not_found(self):
        """测试：Isabelle不存在时应该抛出异常"""
        with pytest.raises(IsabelleNotFoundError):
            IsabelleInterface(isabelle_path="/nonexistent/isabelle")


class TestTheoryNameValidation:
    """Theory名称验证测试"""
    
    @patch('subprocess.run')
    def test_validate_theory_name_valid(self, mock_run):
        """测试：有效的theory名称"""
        mock_result = MagicMock()
        mock_result.returncode = 0
        mock_result.stdout = "Isabelle2023"
        mock_run.return_value = mock_result
        
        interface = IsabelleInterface()
        
        valid_names = [
            "Test_Basic",
            "MyTheory",
            "T123",
            "Valid_Theory_Name_123"
        ]
        
        for name in valid_names:
            result = interface._validate_theory_name(name)
            assert result == name
    
    @patch('subprocess.run')
    @pytest.mark.parametrize("invalid_name", [
        "123Invalid",      # 数字开头
        "_Invalid",        # 下划线开头
        "Invalid-Name",    # 包含连字符
        "Invalid Name",    # 包含空格
        "begin",           # 保留词
        "",                # 空字符串
    ])
    def test_validate_theory_name_invalid(self, mock_run, invalid_name):
        """测试：无效的theory名称"""
        mock_result = MagicMock()
        mock_result.returncode = 0
        mock_result.stdout = "Isabelle2023"
        mock_run.return_value = mock_result
        
        interface = IsabelleInterface()
        
        with pytest.raises(InvalidTheoryNameError):
            interface._validate_theory_name(invalid_name)


class TestFilePathValidation:
    """文件路径验证测试"""
    
    @patch('subprocess.run')
    def test_validate_file_path_success(self, mock_run):
        """测试：验证有效文件路径"""
        mock_result = MagicMock()
        mock_result.returncode = 0
        mock_result.stdout = "Isabelle2023"
        mock_run.return_value = mock_result
        
        # 创建临时文件
        fd, temp_path = tempfile.mkstemp(suffix='.thy')
        os.close(fd)
        
        try:
            interface = IsabelleInterface()
            path = interface._validate_file_path(temp_path)
            assert path.exists()
            assert path.is_file()
        finally:
            os.unlink(temp_path)
    
    @patch('subprocess.run')
    def test_validate_file_path_not_found(self, mock_run):
        """测试：文件不存在时抛出异常"""
        mock_result = MagicMock()
        mock_result.returncode = 0
        mock_result.stdout = "Isabelle2023"
        mock_run.return_value = mock_result
        
        interface = IsabelleInterface()
        
        with pytest.raises(FileNotFoundError):
            interface._validate_file_path("/nonexistent/file.thy")
    
    @patch('subprocess.run')
    def test_validate_file_path_is_directory(self, mock_run, tmpdir):
        """测试：路径是目录时抛出异常"""
        mock_result = MagicMock()
        mock_result.returncode = 0
        mock_result.stdout = "Isabelle2023"
        mock_run.return_value = mock_result
        
        interface = IsabelleInterface()
        
        with pytest.raises(ValueError):
            interface._validate_file_path(str(tmpdir))


class TestCreateTempFile:
    """临时文件创建测试"""
    
    @patch('subprocess.run')
    def test_create_temp_thy_file(self, mock_run):
        """测试：创建临时theory文件"""
        mock_result = MagicMock()
        mock_result.returncode = 0
        mock_result.stdout = "Isabelle2023"
        mock_run.return_value = mock_result
        
        interface = IsabelleInterface()
        content = "theory Test imports Main begin end"
        
        try:
            temp_path = interface._create_temp_thy_file(
                content=content,
                prefix='test_'
            )
            
            assert os.path.exists(temp_path)
            assert temp_path.endswith('.thy')
            
            with open(temp_path) as f:
                assert f.read() == content
        finally:
            if os.path.exists(temp_path):
                os.unlink(temp_path)
    
    @patch('subprocess.run')
    def test_safe_remove_file(self, mock_run):
        """测试：安全删除文件"""
        mock_result = MagicMock()
        mock_result.returncode = 0
        mock_result.stdout = "Isabelle2023"
        mock_run.return_value = mock_result
        
        # 创建临时文件
        fd, temp_path = tempfile.mkstemp()
        os.close(fd)
        
        interface = IsabelleInterface()
        success = interface._safe_remove_file(temp_path)
        
        assert success is True
        assert not os.path.exists(temp_path)
    
    @patch('subprocess.run')
    def test_safe_remove_nonexistent_file(self, mock_run):
        """测试：删除不存在的文件"""
        mock_result = MagicMock()
        mock_result.returncode = 0
        mock_result.stdout = "Isabelle2023"
        mock_run.return_value = mock_result
        
        interface = IsabelleInterface()
        success = interface._safe_remove_file("/nonexistent/file.thy")
        
        assert success is True  # 不存在也视为成功


class TestRunTheory:
    """运行theory测试"""
    
    @patch('subprocess.run')
    def test_run_theory_success(self, mock_run):
        """测试：成功运行theory"""
        # 创建临时theory文件
        fd, temp_path = tempfile.mkstemp(suffix='.thy', prefix='Test_')
        os.write(fd, b'theory Test imports Main begin end')
        os.close(fd)
        
        try:
            # Mock subprocess
            mock_result = MagicMock()
            mock_result.returncode = 0
            mock_result.stdout = "Success"
            mock_result.stderr = ""
            
            call_count = [0]
            def mock_run_side_effect(*args, **kwargs):
                call_count[0] += 1
                if call_count[0] == 1:  # 第一次调用是verify
                    mock_ret = MagicMock()
                    mock_ret.returncode = 0
                    mock_ret.stdout = "Isabelle2023"
                    return mock_ret
                else:  # 后续调用是run_theory
                    return mock_result
            
            mock_run.side_effect = mock_run_side_effect
            
            interface = IsabelleInterface()
            result = interface.run_theory(temp_path, timeout=60.0)
            
            assert result.status == IsabelleStatus.SUCCESS
            assert result.execution_time >= 0
            
        finally:
            os.unlink(temp_path)
    
    @patch('subprocess.run')
    def test_run_theory_timeout(self, mock_run):
        """测试：theory执行超时"""
        # 创建临时theory文件
        fd, temp_path = tempfile.mkstemp(suffix='.thy', prefix='Test_')
        os.close(fd)
        
        try:
            call_count = [0]
            def mock_run_side_effect(*args, **kwargs):
                call_count[0] += 1
                if call_count[0] == 1:  # verify成功
                    mock_ret = MagicMock()
                    mock_ret.returncode = 0
                    mock_ret.stdout = "Isabelle2023"
                    return mock_ret
                else:  # run_theory超时
                    raise subprocess.TimeoutExpired('cmd', 60)
            
            mock_run.side_effect = mock_run_side_effect
            
            interface = IsabelleInterface()
            result = interface.run_theory(temp_path, timeout=60.0)
            
            assert result.status == IsabelleStatus.TIMEOUT
            assert "超时" in result.error
            
        finally:
            os.unlink(temp_path)
    
    @patch('subprocess.run')
    def test_run_theory_file_not_found(self, mock_run):
        """测试：文件不存在"""
        mock_result = MagicMock()
        mock_result.returncode = 0
        mock_result.stdout = "Isabelle2023"
        mock_run.return_value = mock_result
        
        interface = IsabelleInterface()
        
        with pytest.raises(FileNotFoundError):
            interface.run_theory("/nonexistent/file.thy")


class TestBatchTest:
    """批量测试测试"""
    
    @patch('subprocess.run')
    def test_batch_test_empty_list(self, mock_run):
        """测试：空文件列表"""
        mock_result = MagicMock()
        mock_result.returncode = 0
        mock_result.stdout = "Isabelle2023"
        mock_run.return_value = mock_result
        
        interface = IsabelleInterface()
        results = interface.batch_test_theories([])
        
        assert results == {}
    
    @patch('subprocess.run')
    def test_batch_test_single_file(self, mock_run):
        """测试：批量测试单个文件"""
        # 创建临时文件
        fd, temp_path = tempfile.mkstemp(suffix='.thy', prefix='Test_')
        os.close(fd)
        
        try:
            mock_result = MagicMock()
            mock_result.returncode = 0
            mock_result.stdout = "Success"
            mock_result.stderr = ""
            
            call_count = [0]
            def mock_run_side_effect(*args, **kwargs):
                call_count[0] += 1
                if call_count[0] == 1:  # verify
                    mock_ret = MagicMock()
                    mock_ret.returncode = 0
                    mock_ret.stdout = "Isabelle2023"
                    return mock_ret
                else:  # run_theory
                    return mock_result
            
            mock_run.side_effect = mock_run_side_effect
            
            interface = IsabelleInterface()
            results = interface.batch_test_theories([temp_path])
            
            assert len(results) == 1
            assert temp_path in results
            
        finally:
            os.unlink(temp_path)


# ============================================================================
# Pytest配置和fixture
# ============================================================================

@pytest.fixture
def temp_thy_file():
    """创建临时theory文件fixture"""
    fd, path = tempfile.mkstemp(suffix='.thy', prefix='Test_')
    os.write(fd, b'theory Test imports Main begin end')
    os.close(fd)
    yield path
    try:
        os.unlink(path)
    except:
        pass


@pytest.fixture
def mock_subprocess_success():
    """Mock成功的subprocess调用"""
    with patch('subprocess.run') as mock_run:
        mock_result = MagicMock()
        mock_result.returncode = 0
        mock_result.stdout = "Isabelle2023: November 2023"
        mock_result.stderr = ""
        mock_run.return_value = mock_result
        yield mock_run


if __name__ == "__main__":
    # 运行测试
    pytest.main([__file__, "-v", "--cov=code"])

