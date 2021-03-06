module.exports = {
  "roots": [
    "<rootDir>/src"
  ],
  "transform": {
    "^.+\\.tsx?$": "ts-jest"
  },
  "collectCoverage": true,
  "coverageThreshold": {
    "global": {
      "branches": 95.56, // TODO 100%
      "functions": 100,
      "lines": 97.9,
      "statements": 97.91
    }
  }
}
