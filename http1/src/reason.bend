# Every reason a request can be rejected, and the status to send for it.

import Base
import ../../urlpath/src/errors.bend as PathError


type Reason is Data:
  NotAByte{}
  BareLF{}
  BareCR{}
  InvalidRequestLine{}
  InvalidTarget{}
  InvalidPath{error: PathError.PathError}
  InvalidVersion{}
  WhitespaceBeforeColon{}
  WhitespaceBeforeFirstField{}
  ObsFold{}
  InvalidFieldLine{}
  InvalidFieldName{}
  InvalidFieldValue{}
  ContentLengthWithTransferEncoding{}
  TransferEncodingInHttp10{}
  ChunkedNotFinal{}
  ChunkedAppliedTwice{}
  InvalidTransferEncoding{}
  InvalidContentLength{}
  MultipleContentLength{}
  InvalidChunkSize{}
  InvalidChunkExtension{}
  ChunkExtensionTooLong{}
  MissingChunkDataCRLF{}
  MissingHost{}
  DuplicateHost{}
  InvalidHost{}
  HostMismatch{}
  ContentTooLarge{}
  TargetTooLong{}
  UnsupportedExpectation{}
  HeaderTooLarge{}
  TooManyFields{}
  MethodTooLong{}
  MethodNotImplemented{}
  UnsupportedTransferCoding{}
  VersionNotSupported{}

# The status to send before closing the connection
def status(r: Reason) -> U32:
  match r:
    case ContentTooLarge{}:
        413
    case TargetTooLong{}:
        414
    case UnsupportedExpectation{}:
        417
    case HeaderTooLarge{}:
        431
    case TooManyFields{}:
        431
    case MethodTooLong{}:
        501
    case MethodNotImplemented{}:
        501
    case UnsupportedTransferCoding{}:
        501
    case VersionNotSupported{}:
        505
    case other:
        400
