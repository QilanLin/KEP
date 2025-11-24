"""
配置管理示例 - 展示如何管理配置

支持多种配置方式：
1. 代码中的默认配置
2. YAML配置文件
3. 环境变量
4. 命令行参数
"""

import os
import yaml
from dataclasses import dataclass, field, asdict
from pathlib import Path
from typing import Optional, Dict, Any, List
import logging

logger = logging.getLogger(__name__)


@dataclass
class IsabelleConfig:
    """Isabelle相关配置"""
    isabelle_path: str = "isabelle"
    sledgehammer_export_dir: Path = field(
        default_factory=lambda: Path.home() / ".isabelle/sledgehammer/export"
    )
    default_timeout: float = 60.0
    default_prover: str = "e"
    available_provers: List[str] = field(
        default_factory=lambda: ["e", "cvc5", "z3", "vampire", "spass"]
    )
    
    def __post_init__(self):
        """初始化后处理"""
        # 确保Path对象
        if isinstance(self.sledgehammer_export_dir, str):
            self.sledgehammer_export_dir = Path(self.sledgehammer_export_dir).expanduser()


@dataclass
class FuzzerConfig:
    """Fuzzer相关配置"""
    seed_dir: Path = field(default_factory=lambda: Path("../sledgehammer_export"))
    output_dir: Path = field(default_factory=lambda: Path("./fuzzer_results"))
    timeout: float = 30.0
    num_mutants: int = 10
    use_ast_mutator: bool = False
    random_seed: Optional[int] = None
    
    # 种子预过滤
    enable_seed_filtering: bool = True
    seed_filter_timeout: float = 10.0
    
    # 相对执行时间检测
    use_relative_time_check: bool = True
    relative_time_threshold: float = 2.0
    
    # Reconstruction Oracle
    use_reconstruction_oracle: bool = False
    reconstruction_timeout: float = 30.0
    
    # 并发设置
    max_workers: Optional[int] = None
    
    def __post_init__(self):
        """初始化后处理"""
        # 确保Path对象
        if isinstance(self.seed_dir, str):
            self.seed_dir = Path(self.seed_dir)
        if isinstance(self.output_dir, str):
            self.output_dir = Path(self.output_dir)
        
        # 创建输出目录
        self.output_dir.mkdir(parents=True, exist_ok=True)


@dataclass
class LoggingConfig:
    """日志相关配置"""
    log_level: str = "INFO"
    log_file: Optional[Path] = None
    enable_console: bool = True
    log_format: str = "%(asctime)s - %(name)s - %(levelname)s - %(message)s"
    console_format: str = "%(levelname)s: %(message)s"
    
    def __post_init__(self):
        """初始化后处理"""
        if isinstance(self.log_file, str):
            self.log_file = Path(self.log_file)


@dataclass
class Config:
    """
    主配置类
    
    整合所有配置项，支持多种加载方式
    """
    isabelle: IsabelleConfig = field(default_factory=IsabelleConfig)
    fuzzer: FuzzerConfig = field(default_factory=FuzzerConfig)
    logging: LoggingConfig = field(default_factory=LoggingConfig)
    
    # 元数据
    config_file: Optional[Path] = None
    
    @classmethod
    def from_defaults(cls) -> 'Config':
        """
        使用默认配置创建
        
        Returns:
            Config实例
        """
        return cls()
    
    @classmethod
    def from_yaml(cls, config_file: str) -> 'Config':
        """
        从YAML文件加载配置
        
        Args:
            config_file: YAML配置文件路径
            
        Returns:
            Config实例
            
        Raises:
            FileNotFoundError: 配置文件不存在
            yaml.YAMLError: YAML格式错误
        """
        config_path = Path(config_file)
        
        if not config_path.exists():
            raise FileNotFoundError(f"配置文件不存在: {config_file}")
        
        logger.info(f"从文件加载配置: {config_file}")
        
        with open(config_path) as f:
            data = yaml.safe_load(f)
        
        # 解析配置
        isabelle_config = IsabelleConfig(**data.get('isabelle', {}))
        fuzzer_config = FuzzerConfig(**data.get('fuzzer', {}))
        logging_config = LoggingConfig(**data.get('logging', {}))
        
        return cls(
            isabelle=isabelle_config,
            fuzzer=fuzzer_config,
            logging=logging_config,
            config_file=config_path
        )
    
    @classmethod
    def from_env(cls) -> 'Config':
        """
        从环境变量加载配置
        
        环境变量格式:
            ISABELLE_PATH
            ISABELLE_TIMEOUT
            FUZZER_SEED_DIR
            FUZZER_OUTPUT_DIR
            LOG_LEVEL
            等等
        
        Returns:
            Config实例
        """
        logger.info("从环境变量加载配置")
        
        isabelle_config = IsabelleConfig(
            isabelle_path=os.getenv('ISABELLE_PATH', 'isabelle'),
            default_timeout=float(os.getenv('ISABELLE_TIMEOUT', '60.0')),
            default_prover=os.getenv('ISABELLE_PROVER', 'e'),
        )
        
        fuzzer_config = FuzzerConfig(
            seed_dir=Path(os.getenv('FUZZER_SEED_DIR', '../sledgehammer_export')),
            output_dir=Path(os.getenv('FUZZER_OUTPUT_DIR', './fuzzer_results')),
            timeout=float(os.getenv('FUZZER_TIMEOUT', '30.0')),
            num_mutants=int(os.getenv('FUZZER_NUM_MUTANTS', '10')),
        )
        
        logging_config = LoggingConfig(
            log_level=os.getenv('LOG_LEVEL', 'INFO'),
            log_file=Path(os.getenv('LOG_FILE')) if os.getenv('LOG_FILE') else None,
        )
        
        return cls(
            isabelle=isabelle_config,
            fuzzer=fuzzer_config,
            logging=logging_config
        )
    
    @classmethod
    def from_dict(cls, data: Dict[str, Any]) -> 'Config':
        """
        从字典创建配置
        
        Args:
            data: 配置字典
            
        Returns:
            Config实例
        """
        isabelle_config = IsabelleConfig(**data.get('isabelle', {}))
        fuzzer_config = FuzzerConfig(**data.get('fuzzer', {}))
        logging_config = LoggingConfig(**data.get('logging', {}))
        
        return cls(
            isabelle=isabelle_config,
            fuzzer=fuzzer_config,
            logging=logging_config
        )
    
    def to_dict(self) -> Dict[str, Any]:
        """
        转换为字典
        
        Returns:
            配置字典
        """
        return {
            'isabelle': asdict(self.isabelle),
            'fuzzer': asdict(self.fuzzer),
            'logging': asdict(self.logging)
        }
    
    def to_yaml(self, output_file: str) -> None:
        """
        保存为YAML文件
        
        Args:
            output_file: 输出文件路径
        """
        data = self.to_dict()
        
        # 转换Path为字符串以便YAML序列化
        def convert_paths(obj):
            if isinstance(obj, dict):
                return {k: convert_paths(v) for k, v in obj.items()}
            elif isinstance(obj, list):
                return [convert_paths(item) for item in obj]
            elif isinstance(obj, Path):
                return str(obj)
            return obj
        
        data = convert_paths(data)
        
        with open(output_file, 'w') as f:
            yaml.dump(data, f, default_flow_style=False, sort_keys=False)
        
        logger.info(f"配置已保存到: {output_file}")
    
    def validate(self) -> List[str]:
        """
        验证配置的有效性
        
        Returns:
            错误消息列表（空列表表示验证通过）
        """
        errors = []
        
        # 验证Isabelle配置
        if self.isabelle.default_timeout <= 0:
            errors.append("Isabelle timeout必须大于0")
        
        if not self.isabelle.default_prover:
            errors.append("必须指定默认prover")
        
        if self.isabelle.default_prover not in self.isabelle.available_provers:
            errors.append(
                f"默认prover '{self.isabelle.default_prover}' "
                f"不在可用provers列表中"
            )
        
        # 验证Fuzzer配置
        if self.fuzzer.timeout <= 0:
            errors.append("Fuzzer timeout必须大于0")
        
        if self.fuzzer.num_mutants <= 0:
            errors.append("Mutants数量必须大于0")
        
        if self.fuzzer.relative_time_threshold <= 1.0:
            errors.append("相对时间阈值必须大于1.0")
        
        # 验证日志配置
        valid_log_levels = ['DEBUG', 'INFO', 'WARNING', 'ERROR', 'CRITICAL']
        if self.logging.log_level.upper() not in valid_log_levels:
            errors.append(
                f"无效的日志级别: {self.logging.log_level}. "
                f"有效值: {', '.join(valid_log_levels)}"
            )
        
        return errors
    
    def setup_logging(self) -> None:
        """根据配置设置日志系统"""
        handlers = []
        
        # 文件handler
        if self.logging.log_file:
            file_handler = logging.FileHandler(
                self.logging.log_file,
                encoding='utf-8'
            )
            file_handler.setLevel(logging.DEBUG)
            file_formatter = logging.Formatter(self.logging.log_format)
            file_handler.setFormatter(file_formatter)
            handlers.append(file_handler)
        
        # 控制台handler
        if self.logging.enable_console:
            console_handler = logging.StreamHandler()
            console_handler.setLevel(
                getattr(logging, self.logging.log_level.upper())
            )
            console_formatter = logging.Formatter(self.logging.console_format)
            console_handler.setFormatter(console_formatter)
            handlers.append(console_handler)
        
        # 配置root logger
        logging.basicConfig(
            level=logging.DEBUG,
            handlers=handlers
        )
        
        logger.info("日志系统已配置")


# ============================================================================
# 配置管理器（单例模式）
# ============================================================================

class ConfigManager:
    """
    配置管理器（单例）
    
    提供全局配置访问
    """
    _instance: Optional['ConfigManager'] = None
    _config: Optional[Config] = None
    
    def __new__(cls):
        if cls._instance is None:
            cls._instance = super().__new__(cls)
        return cls._instance
    
    @classmethod
    def get_instance(cls) -> 'ConfigManager':
        """获取单例实例"""
        if cls._instance is None:
            cls._instance = cls()
        return cls._instance
    
    def load_config(self, 
                   config_file: Optional[str] = None,
                   use_env: bool = False) -> Config:
        """
        加载配置
        
        Args:
            config_file: YAML配置文件路径（优先级最高）
            use_env: 是否从环境变量加载
            
        Returns:
            Config实例
        """
        if config_file:
            self._config = Config.from_yaml(config_file)
        elif use_env:
            self._config = Config.from_env()
        else:
            self._config = Config.from_defaults()
        
        # 验证配置
        errors = self._config.validate()
        if errors:
            raise ValueError(
                f"配置验证失败:\n" + "\n".join(f"- {err}" for err in errors)
            )
        
        # 设置日志
        self._config.setup_logging()
        
        return self._config
    
    def get_config(self) -> Config:
        """
        获取当前配置
        
        Returns:
            Config实例
            
        Raises:
            RuntimeError: 配置未加载
        """
        if self._config is None:
            raise RuntimeError("配置未加载，请先调用load_config()")
        return self._config


# ============================================================================
# 使用示例
# ============================================================================

def example_usage():
    """配置管理使用示例"""
    print("=" * 60)
    print("配置管理示例")
    print("=" * 60)
    
    # 方式1: 使用默认配置
    print("\n1️⃣ 使用默认配置:")
    config1 = Config.from_defaults()
    print(f"   Isabelle路径: {config1.isabelle.isabelle_path}")
    print(f"   默认timeout: {config1.isabelle.default_timeout}秒")
    print(f"   日志级别: {config1.logging.log_level}")
    
    # 方式2: 从YAML文件加载
    print("\n2️⃣ 从YAML文件加载配置:")
    # 首先创建示例配置文件
    config1.to_yaml('example_config.yaml')
    print("   ✅ 已创建example_config.yaml")
    
    config2 = Config.from_yaml('example_config.yaml')
    print(f"   加载成功: {config2.config_file}")
    
    # 方式3: 从环境变量加载
    print("\n3️⃣ 从环境变量加载配置:")
    os.environ['ISABELLE_PATH'] = '/usr/local/bin/isabelle'
    os.environ['LOG_LEVEL'] = 'DEBUG'
    config3 = Config.from_env()
    print(f"   Isabelle路径: {config3.isabelle.isabelle_path}")
    print(f"   日志级别: {config3.logging.log_level}")
    
    # 方式4: 从字典创建
    print("\n4️⃣ 从字典创建配置:")
    config_dict = {
        'isabelle': {
            'isabelle_path': 'custom_isabelle',
            'default_timeout': 120.0
        },
        'fuzzer': {
            'num_mutants': 20,
            'use_ast_mutator': True
        }
    }
    config4 = Config.from_dict(config_dict)
    print(f"   Mutants数量: {config4.fuzzer.num_mutants}")
    print(f"   使用AST mutator: {config4.fuzzer.use_ast_mutator}")
    
    # 验证配置
    print("\n5️⃣ 验证配置:")
    errors = config4.validate()
    if errors:
        print(f"   ❌ 验证失败:")
        for err in errors:
            print(f"      - {err}")
    else:
        print("   ✅ 配置有效")
    
    # 使用ConfigManager（单例）
    print("\n6️⃣ 使用ConfigManager:")
    manager = ConfigManager.get_instance()
    manager.load_config(config_file='example_config.yaml')
    config = manager.get_config()
    print(f"   ✅ 全局配置已加载")
    print(f"   Fuzzer输出目录: {config.fuzzer.output_dir}")
    
    print("\n" + "=" * 60)
    print("✅ 配置管理示例完成")
    print("=" * 60)


if __name__ == "__main__":
    example_usage()

