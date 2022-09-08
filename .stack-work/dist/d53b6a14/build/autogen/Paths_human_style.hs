{-# LANGUAGE CPP #-}
{-# LANGUAGE NoRebindableSyntax #-}
{-# OPTIONS_GHC -fno-warn-missing-import-lists #-}
{-# OPTIONS_GHC -Wno-missing-safe-haskell-mode #-}
module Paths_human_style (
    version,
    getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir,
    getDataFileName, getSysconfDir
  ) where

import qualified Control.Exception as Exception
import Data.Version (Version(..))
import System.Environment (getEnv)
import Prelude

#if defined(VERSION_base)

#if MIN_VERSION_base(4,0,0)
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#else
catchIO :: IO a -> (Exception.Exception -> IO a) -> IO a
#endif

#else
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#endif
catchIO = Exception.catch

version :: Version
version = Version [0,1,0,0] []
bindir, libdir, dynlibdir, datadir, libexecdir, sysconfdir :: FilePath

bindir     = "C:\\Users\\wills\\Desktop\\ATP Project\\Haskell\\prototype\\.stack-work\\install\\95222539\\bin"
libdir     = "C:\\Users\\wills\\Desktop\\ATP Project\\Haskell\\prototype\\.stack-work\\install\\95222539\\lib\\x86_64-windows-ghc-9.0.2\\human-style-0.1.0.0-55DlATS5bdkJpQF7llWars"
dynlibdir  = "C:\\Users\\wills\\Desktop\\ATP Project\\Haskell\\prototype\\.stack-work\\install\\95222539\\lib\\x86_64-windows-ghc-9.0.2"
datadir    = "C:\\Users\\wills\\Desktop\\ATP Project\\Haskell\\prototype\\.stack-work\\install\\95222539\\share\\x86_64-windows-ghc-9.0.2\\human-style-0.1.0.0"
libexecdir = "C:\\Users\\wills\\Desktop\\ATP Project\\Haskell\\prototype\\.stack-work\\install\\95222539\\libexec\\x86_64-windows-ghc-9.0.2\\human-style-0.1.0.0"
sysconfdir = "C:\\Users\\wills\\Desktop\\ATP Project\\Haskell\\prototype\\.stack-work\\install\\95222539\\etc"

getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir, getSysconfDir :: IO FilePath
getBinDir = catchIO (getEnv "human_style_bindir") (\_ -> return bindir)
getLibDir = catchIO (getEnv "human_style_libdir") (\_ -> return libdir)
getDynLibDir = catchIO (getEnv "human_style_dynlibdir") (\_ -> return dynlibdir)
getDataDir = catchIO (getEnv "human_style_datadir") (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "human_style_libexecdir") (\_ -> return libexecdir)
getSysconfDir = catchIO (getEnv "human_style_sysconfdir") (\_ -> return sysconfdir)

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir ++ "\\" ++ name)
