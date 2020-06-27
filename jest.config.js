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
      "branches": 97.47, // TODO 100%
      "functions": 100,
      "lines": 100,
      "statements": 100
    }
  }
}
